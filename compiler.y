/* Please feel free to modify any content */

/* Definition section */
%{
    #include "compiler_common.h" //Extern variables that communicate with lex
    // #define YYDEBUG 1
    // int yydebug = 1;

    extern int yylineno;
    extern int yylex();
    extern FILE *yyin;
    FILE *out;
    char out_buff[1024];

    int yylex_destroy();
    static char *make_yyerr(char *err, char *name){
        char *yyerr = malloc(sizeof(char) * 1024);

        sprintf(yyerr, "%s: %s", err, name);

        return yyerr;
    }
    void yyerror(char const *s)
    {
        printf("error:%d: %s\n", yylineno + 1, s);
    }

    extern int yylineno;
    extern int yylex();
    extern FILE *yyin;

    /* Symbol table function - you can add new functions if needed. */
    /* parameters and return type can be changed */
    static void create_symbol();
    static void insert_symbol(char *name, char *type, char *fun_sig, int mut);
    static struct symbol *lookup_symbol();
    static void update_symbol(char *name);
    static void dump_symbol();

    /* Global variables */
    bool HAS_ERROR = false;

    static int scope_level = 0;
    static int addr = -1;
    static int slient = 0;
    static char *parsing_func;

    typedef struct symbol
    {
        int Index, Mut, Addr, Lineno;
        char *Name, *Type, *Func_sig;
    } Symbol;

    typedef struct dynamic_array
    {
        Symbol *data;
        size_t size;
        size_t capacity;
    } DynamicArray;

    void dynamic_array_init(DynamicArray *arr, size_t initial_capacity)
    {
        arr->data = (Symbol *)malloc(initial_capacity * sizeof(Symbol));
        arr->size = 0;
        arr->capacity = initial_capacity;
    }

    void dynamic_array_resize(DynamicArray *arr, size_t new_capacity)
    {
        Symbol *new_data = (Symbol *)realloc(arr->data, new_capacity * sizeof(Symbol));
        if (new_data == NULL)
        {
            printf("Failed to resize dynamic array.\n");
            return;
        }

        arr->data = new_data;
        arr->capacity = new_capacity;
    }

    void dynamic_array_append(DynamicArray *arr, Symbol symbol)
    {
        if (arr->size == arr->capacity)
        {
            size_t new_capacity = arr->capacity * 2;
            dynamic_array_resize(arr, new_capacity);
        }

        arr->data[arr->size] = symbol;
        arr->size++;
    }

    void dynamic_array_free(DynamicArray *arr)
    {
        free(arr->data);
        arr->data = NULL;
        arr->size = 0;
        arr->capacity = 0;
    }

    DynamicArray **tables;

    void func_init(){
        addr = -1; 
        for(int i = 0; i < scope_level; i++){
            if(tables[i] != NULL){
                dynamic_array_free(tables[i]);
                tables[i] = NULL;
            }
        }
        scope_level = 0;
    }

    void append_func_sig(char *type, int isClosePareness){
        Symbol *symbol = lookup_symbol(parsing_func);
        if(!strcmp(symbol->Func_sig, ("(V)V"))){
            symbol->Func_sig = malloc(sizeof(char) * 1024);
            strcpy(symbol->Func_sig, "(");
        }
        if(isClosePareness)
            strcat(symbol->Func_sig, ")");

        if(!strcmp(type, "i32")) strcat(symbol->Func_sig, "I");
        if(!strcmp(type, "str")) strcat(symbol->Func_sig, "S");
        if(!strcmp(type, "f32")) strcat(symbol->Func_sig, "F");
        if(!strcmp(type, "bool")) strcat(symbol->Func_sig, "B");

    }

    void dump_code_gen(char *s){
        fprintf(out, "%s\n", s);
    }
    
    void make_out_header(){
        dump_code_gen(".class public Main");
        dump_code_gen(".super java/lang/Object");
        dump_code_gen(".method public static main([Ljava/lang/String;)V");
        dump_code_gen(".limit stack 1024");
        dump_code_gen(".limit locals 1024");
    }

    void make_out_footer(){
        dump_code_gen("return");
        dump_code_gen(".end method");
    }

    static int lc = 0;

    void printer(char *type, int isNewLine){
        if(!strcmp(type, "bool")){
            sprintf(out_buff, "ifeq label%d\nldc \"true\"\ngoto endLabel%d\nlabel%d:\nldc \"false\"\nendLabel%d:", lc, lc, lc, lc);
            dump_code_gen(out_buff);
            lc++;
        }

        dump_code_gen("getstatic java/lang/System/out Ljava/io/PrintStream;");
        dump_code_gen("swap");   // LR will trigger literal or expr first so need to swap two command

        if(!strcmp(type, "str") || !strcmp(type, "bool"))
            sprintf(out_buff, "invokevirtual java/io/PrintStream/%s(Ljava/lang/String;)V", isNewLine ? "println": "print");
        
        if(!strcmp(type, "f32"))
            sprintf(out_buff, "invokevirtual java/io/PrintStream/%s(F)V", isNewLine ? "println": "print");

        if(!strcmp(type, "i32"))
            sprintf(out_buff, "invokevirtual java/io/PrintStream/%s(I)V", isNewLine ? "println": "print");
    
        dump_code_gen(out_buff);
    }

    char type_simplify(char *type){
        if(!strcmp(type, "i32"))
            return 'i';
        if(!strcmp(type, "f32"))
            return 'f';
        return ' ';
    }

    void operand(char op, char *type){
        switch(op){
            case '+':
                sprintf(out_buff, "%cadd", type_simplify(type));
                break;
            case '-':
                sprintf(out_buff, "%csub", type_simplify(type));
                break;
            case '*':
                sprintf(out_buff, "%cmul", type_simplify(type));
                break;
            case '/':
                sprintf(out_buff, "%cdiv", type_simplify(type));
                break;
            case '%':
                sprintf(out_buff, "%crem", type_simplify(type));
                break;
            case 'A':
                sprintf(out_buff, "iand");
                break;
            case 'O':
                sprintf(out_buff, "ior");
                break;
            case '!':
                sprintf(out_buff, "ifeq label%d\nldc 0\ngoto endLabel%d\nlabel%d:\nldc 1\nendLabel%d:", lc, lc, lc, lc);
                lc++;
                break;
            case '>':
                sprintf(out_buff, "%s label%d\nldc 0\ngoto endLabel%d\nlabel%d:\nldc 1\nendLabel%d:",!strcmp(type, "f32") ? "fcmpg\nifgt" : "if_icmpgt", lc, lc, lc, lc);
                lc++;
                break;
                
            case '<':
                sprintf(out_buff, "%s label%d\nldc 0\ngoto endLabel%d\nlabel%d:\nldc 1\nendLabel%d:",!strcmp(type, "f32") ? "fcmpl\niflt" : "if_icmplt", lc, lc, lc, lc);
                lc++;
                break;

            case 'E':
                sprintf(out_buff, "%s label%d\nldc 0\ngoto endLabel%d\nlabel%d:\nldc 1\nendLabel%d:", !strcmp(type, "f32") ? "fcmpl\nifne" : "if_icmpeq", lc, lc, lc, lc);
                lc++;
                break;

            case 'N':
                sprintf(out_buff, "%s label%d\nldc 1\ngoto endLabel%d\nlabel%d:\nldc 0\nendLabel%d:", !strcmp(type, "f32") ? "fcmpl\nifne" : "if_icmpeq", lc, lc, lc, lc);
                lc++;
                break;

            case 'G':
                sprintf(out_buff, "%s label%d\nldc 0\ngoto endLabel%d\nlabel%d:\nldc 1\nendLabel%d:", !strcmp(type, "f32") ? "fcmpg\nifgt" : "if_icmpge", lc, lc, lc, lc);
                lc++;
                break;

            case 'L':
                sprintf(out_buff, "%s label%d\nldc 0\ngoto endLabel%d\nlabel%d:\nldc 1\nendLabel%d:", !strcmp(type, "f32") ? "fcmpl\nifle" : "if_icmple", lc, lc, lc, lc);
                lc++;
                break;
        }
        dump_code_gen(out_buff);
    }

    void store(int addr, char *type){
        if(!strcmp(type, "i32") || !strcmp(type, "bool"))
        sprintf(out_buff, "istore %d", addr);

        if(!strcmp(type, "str"))
            sprintf(out_buff, "astore %d", addr);
            
        if(!strcmp(type, "f32"))
            sprintf(out_buff, "fstore %d", addr);

        dump_code_gen(out_buff);
    }

    void load(Symbol *symbol){
        char *type = symbol->Type;
        int addr = symbol->Addr;

        if(!strcmp(type, "i32") || !strcmp(type, "bool"))
            sprintf(out_buff, "iload %d", addr);

        if(!strcmp(type, "str"))
            sprintf(out_buff, "aload %d", addr);
            
        if(!strcmp(type, "f32"))
            sprintf(out_buff, "fload %d", addr);

        dump_code_gen(out_buff);
    }

    char label_comparand(char *s){
        if(!strcmp(s,"EQL")) return 'E';
        if(!strcmp(s,"NEQ")) return 'N';
        if(!strcmp(s,"GTR")) return '>';
        if(!strcmp(s,"LSS")) return '<';
        if(!strcmp(s,"GEQ")) return 'G';
        if(!strcmp(s,"LEQ")) return 'L';
        return ' ';
    }
%}


/* %error-verbose */

/* Use variable or self-defined structure to represent
* nonterminal and token type
*  - you can add new fields if needed.
*/
%union{
    int i_val;
    float f_val;
    char *s_val;
    void *type;
    bool b_val;
    /* ... */
}

/* Token without return */
%token LET MUT NEWLINE 
%token<i_val> INT INT_LIT 
%token<f_val> FLOAT FLOAT_LIT
%token<s_val> ID STR STRING_LIT
%token <b_val> BOOL TRUE FALSE 
%token GEQ LEQ EQL NEQ LOR LAND 
%token ADD_ASSIGN SUB_ASSIGN MUL_ASSIGN DIV_ASSIGN REM_ASSIGN 
%token IF ELSE FOR WHILE LOOP 
%token PRINT PRINTLN 
%token FUNC RETURN BREAK 
%token ARROW AS IN DOTDOT RSHIFT LSHIFT

%type<i_val> BoolLit
%type<s_val> Printable Lit ComparisonOperator LogicalTerm1 LogicalTermPrime1 Type VariableTypeDcl FuncCall VariableDcl VariableExpr
%type<s_val> Factor Term TermPrime LogicalFactor LogicalTerm LogicalTermPrime ExprPrime Expr ArithmeticExpressionPrime ArithmeticExpression Comparison

/* Yacc will start at this nonterminal */
%start Program

/* Grammar section */
%%

Program
    : GlobalStatementList
;

GlobalStatementList
    : GlobalStatementList GlobalStatement 
    | GlobalStatement
;

GlobalStatement
    : FunctionDeclStmt GlobalStatement
    | FunctionDeclStmt
    | 
;

FunctionDeclStmt
    : FuncDcl '(' TypeList ')' FuncDclTerm                              { func_init(); }

FuncDclTerm
    : Scope
    | ARROW Type Scope                                                  { append_func_sig($2, 1); }
;

FuncDcl
    : FUNC ID                                                           { printf("func: %s\n", $2); insert_symbol($2, "func", "(V)V", -1); slient = 1; scope_level++; create_symbol(); parsing_func = $2;};

TypeList
    : TypeList ',' ID ':' Type                                          { insert_symbol($3, $5, "-", 0); append_func_sig($5, 0); }
    | ID ':' Type                                                       { insert_symbol($1, $3, "-", 0); append_func_sig($3, 0); }              
    |
;

DeclList
    : VariableDcl DeclList
    | VariableDcl
    | VariableExpr DeclList
    | VariableExpr         
    | PrintExpr DeclList
    | PrintExpr
    | Scope DeclList
    | Scope
    | IfExpr DeclList
    | IfExpr
    | WhileExpr DeclList
    | WhileExpr
    | ReturnExpr DeclList
    | ReturnExpr
    | BreakExpr DeclList
    | BreakExpr
    | ForExpr DeclList
    | ForExpr                  
    | Expr                                                              { puts("breturn"); }
;

ForExpr
    : FOR ID IN Expr                                                    { slient = 1; scope_level++; create_symbol(); insert_symbol($2, "i32", "-", 0); } Scope             
;

BreakExpr
    : BREAK Expr ';'              
;

ReturnExpr
    : RETURN Expr ';'                                                   { puts("breturn"); }
;

WhileExpr
    : WHILE Expr Scope
;

IfExpr 
    : IF Expr Scope
    | IF Expr Scope ELSE Scope
;

PrintExpr
    : PRINTLN '(' Printable ')' ';'                                     { printf("PRINTLN %s\n", $3); printer($3, 1); }
    | PRINT '(' Printable ')' ';'                                       { printf("PRINT %s\n", $3); printer($3, 0);};
;

Printable
    : Expr                                                              { $$ = $1; }
;

Expr
    : LogicalTerm ExprPrime                                             { $$ = $1; }
;

Type
    : INT                                                               { $$ = "i32"; }
    | FLOAT                                                             { $$ = "f32"; }
    | BOOL                                                              { $$ = "bool"; }
    | STR                                                               { $$ = "bool"; }
;

ExprPrime 
    : LOR LogicalTerm { operand('O', $2); } ExprPrime                                         { $$ = $2; }
    | 
;

LogicalTerm
    : LogicalTerm1 LogicalTermPrime                                     { $$ = $1; }
;

LogicalTermPrime
    : LAND LogicalTerm1 { operand('A', $2); } LogicalTermPrime                                { $$ = $2; }
    |
;

LogicalTerm1
    :  LogicalFactor LogicalTermPrime1                                  { $$ = $1; }
;

LogicalTermPrime1
    : '!' LogicalFactor LogicalTermPrime1                               { operand('!', $2); $$ = $2; }
    |
;

LogicalFactor
    : Comparison                                                        { $$ = $1; }
    | Lit                                                               { $$ = $1; }
    | '(' Expr ')'                                                      { $$ = $2; }
;

Comparison
    : ArithmeticExpression ComparisonOperator ArithmeticExpression      {   
                                                                            if(strcmp($2, "")){ 
                                                                                if(!strcmp("undefined", $1) || !strcmp("undefined", $3)){
                                                                                    char msg[1024];
                                                                                    sprintf(msg, "%s (mismatched types %s and %s)", $2, $1, $3);
                                                                                    yyerror(make_yyerr("invalid operation", msg));
                                                                                }
                                                                                { 
                                                                                    if (!strcmp($1, "f32") && !strcmp($3, "f32")){
                                                                                        if(strcmp($1, "f32") && !strcmp($3, "f32")){
                                                                                            dump_code_gen("swap\ni2f\nswap");
                                                                                        }
                                                                                        if(!strcmp($1, "f32") && strcmp($3, "f32")){
                                                                                            dump_code_gen("i2f");
                                                                                        }
                                                                                        operand(label_comparand($2), "f32"); 
                                                                                    }
                                                                                    else{
                                                                                        if(strcmp($1, "f32") && !strcmp($3, "f32")){
                                                                                            dump_code_gen("f2i");
                                                                                        }
                                                                                        if(!strcmp($1, "f32") && strcmp($3, "f32")){
                                                                                            dump_code_gen("swap\nf2i\nswap");
                                                                                        }
                                                                                        operand(label_comparand($2), "bool"); 
                                                                                    }
                                                                                } 
                                                                            }
                                                                            $$ = strcmp($2, "") ? "bool" : $1; 
                                                                        }
;

ComparisonOperator
    : EQL                                                               { $$ = "EQL"; }
    | NEQ                                                               { $$ = "NEQ"; } 
    | '>'                                                               { $$ = "GTR"; }
    | '<'                                                               { $$ = "LSS"; }
    | GEQ                                                               { $$ = "GEQ"; } 
    | LEQ                                                               { $$ = "LEQ"; }
    |                                                                   { $$ = ""; }
;


ArithmeticExpression
    : Term ArithmeticExpressionPrime                                         { $$ = $1; }
    | Term LSHIFT Term  { 
                            if(strcmp($1, "i32") || strcmp($3, "i32")){
                                char msg[1024];
                                sprintf(msg, "%s (mismatched types %s and %s)", "LSHIFT", $1, $3);
                                yyerror(make_yyerr("invalid operation", msg));
                            }
                            printf("LSHIFT\n");
                        } 
      ArithmeticExpressionPrime      { $$ = $1; }        
    | Term RSHIFT Term  { 
                            if(strcmp($1, "i32") || strcmp($3, "i32")){
                                char msg[1024];
                                sprintf(msg, "%s (mismatched types %s and %s)", "LSHIFT", $1, $3);
                                yyerror(make_yyerr("invalid operation", msg));
                            }
                            printf("RSHIFT\n");
                        } 
    ArithmeticExpressionPrime      { $$ = $1; }    
;

ArithmeticExpressionPrime
    : '+' Term { operand('+', $2); } ArithmeticExpressionPrime            { $$ = $2; } 
    | '-' Term { operand('-', $2); } ArithmeticExpressionPrime            { $$ = $2; }              
    |            
;

Term 
    : Factor TermPrime                                                  { $$ = $1; }
;                   
                    
TermPrime                   
    : '*' Factor { operand('*', $2); } TermPrime                         { $$ = $2;  }
    | '/' Factor { operand('/', $2); } TermPrime                         { $$ = $2; }
    | '%' Factor { operand('%', $2); } TermPrime                         { $$ = $2; }
    |
;

Factor
    : ID                                                                { Symbol *symbol = lookup_symbol($1); if(symbol) { load(symbol); $$ = symbol->Type; } else {yyerror(make_yyerr("undefined", $1)); $$ = "undefined";} }
    | ID AS Type                                                        {  
                                                                            Symbol *symbol = lookup_symbol($1);
                                                                            if(symbol) {
                                                                                printf("IDENT (name=%s, address=%d)\n", symbol->Name, symbol->Addr); 
                                                                                char *type = symbol->Type;
                                                                                if(!strcmp(type, "f32") && !strcmp($3, "i32")) 
                                                                                    puts("f2i"); 
                                                                                else if(!strcmp(type, "i32") && !strcmp($3, "f32")) 
                                                                                    puts("i2f"); 
                                                                                else
                                                                                    printf("Err %s %s\n",type,$3);

                                                                                $$ = symbol->Type;
                                                                            }
                                                                            else{
                                                                                yyerror(make_yyerr("undefined", $1)); 
                                                                                $$ = "undefined";
                                                                            }
                                                                        }
    | Lit                                                               { $$ = $1; }
    | Lit AS Type                                                       {  
                                                                            if(!strcmp($1, "f32") && !strcmp($3, "i32")) 
                                                                                puts("f2i"); 
                                                                            else if(!strcmp($1, "i32") && !strcmp($3, "f32")) 
                                                                                puts("i2f"); 
                                                                            else
                                                                                printf("Err %s %s\n",$1,$3);

                                                                            $$ = $1;
                                                                        }
    | '(' Expr ')'                                                      { $$ = $2; }
    | '(' Expr ')'  AS Type                                             {  
                                                                            if(!strcmp($2, "f32") && !strcmp($5, "i32")) 
                                                                                puts("f2i"); 
                                                                            else if(!strcmp($2, "i32") && !strcmp($5, "f32")) 
                                                                                puts("i2f"); 
                                                                            else
                                                                                printf("Err %s %s\n",$2,$5);

                                                                            $$ = $2;
                                                                        }
    | FuncCall
    | ID                                                                { Symbol *symbol = lookup_symbol($1); if(symbol) printf("IDENT (name=%s, address=%d)\n", symbol->Name, symbol->Addr); else yyerror(make_yyerr("undefined", $1)); }
        '[' Expr ']'                                                    { Symbol *symbol = lookup_symbol($1); $$ = symbol ? "array" : "undefined"; }
    | LOOP Scope
    | ID                                                                { Symbol *symbol = lookup_symbol($1); if(symbol) printf("IDENT (name=%s, address=%d)\n", symbol->Name, symbol->Addr); else yyerror(make_yyerr("undefined", $1)); }
        '[' Expr DOTDOT { puts("DOTDOT"); } Expr ']'                    { Symbol *symbol = lookup_symbol($1); $$ = symbol ? "array" : "undefined"; }
    | '&' ID                                                            { Symbol *symbol = lookup_symbol($2); if(symbol) printf("IDENT (name=%s, address=%d)\n", symbol->Name, symbol->Addr); else yyerror(make_yyerr("undefined", $2)); }
        '[' Expr DOTDOT { puts("DOTDOT"); } Expr ']'                    { Symbol *symbol = lookup_symbol($2); $$ = symbol ? "array" : "undefined"; }
    |
;

Lit
    : BoolLit                                                           { sprintf(out_buff, "ldc %d", $1); dump_code_gen(out_buff); $$ = "bool"; }
    | INT_LIT                                                           { sprintf(out_buff, "ldc %d", $1); dump_code_gen(out_buff); $$ = "i32"; }
    | '-' INT_LIT                                                       { sprintf(out_buff, "ldc -%d", $2); dump_code_gen(out_buff); $$ = "i32"; }
    | FLOAT_LIT                                                         { sprintf(out_buff, "ldc %f", $1); dump_code_gen(out_buff); $$ = "f32"; }
    | '-' FLOAT_LIT                                                     { sprintf(out_buff, "ldc -%f", $2); dump_code_gen(out_buff); $$ = "f32"; }
    | '"' STRING_LIT '"'                                                { sprintf(out_buff, "ldc \"%s\"", $2); dump_code_gen(out_buff); $$ = "str";}
    | '"' '"'                                                           { sprintf(out_buff, "ldc \"\""); dump_code_gen(out_buff); $$ = "str"; }
;                       

BoolLit                     
    : TRUE                                                              { $$ = 1; }
    | FALSE                                                             { $$ = 0; }
;

VariableDcl
    : LET ID VariableTypeDcl                                            { insert_symbol($2, $3, "-", 0); }  
    | LET MUT ID VariableTypeDcl                                        { insert_symbol($3, $4, "-", 1); }  

    | LET MUT ID ':' INT ';'                                            { insert_symbol($3, "i32", "-1", 1); }  
    | LET MUT ID ':' FLOAT ';'                                          { insert_symbol($3, "f32", "-1", 1); }
    | LET MUT ID ':' BOOL ';'                                           { insert_symbol($3, "bool", "-1", 1); }
    | LET MUT ID ':' '&' STR ';'                                        { insert_symbol($3, "str", "-1", 1); }
;

VariableExpr
    : ID '=' Expr ';'                                                   { Symbol *symbol = lookup_symbol($1); if(symbol) { store(symbol->Addr, symbol->Type); update_symbol($1); $$ = symbol->Type; } else yyerror(make_yyerr("undefined", $1)); $$ = "undefined"; }
    | ID ADD_ASSIGN Expr ';'                                            { Symbol *symbol = lookup_symbol($1); if(symbol) { load(symbol); dump_code_gen("swap"); operand('+', symbol->Type); store(symbol->Addr, symbol->Type); update_symbol($1); $$ = symbol->Type; } else yyerror(make_yyerr("undefined", $1)); $$ = "undefined"; }
    | ID SUB_ASSIGN Expr ';'                                            { Symbol *symbol = lookup_symbol($1); if(symbol) { load(symbol); dump_code_gen("swap"); operand('-', symbol->Type); store(symbol->Addr, symbol->Type); update_symbol($1); $$ = symbol->Type; } else yyerror(make_yyerr("undefined", $1)); $$ = "undefined"; }
    | ID MUL_ASSIGN Expr ';'                                            { Symbol *symbol = lookup_symbol($1); if(symbol) { load(symbol); dump_code_gen("swap"); operand('*', symbol->Type); store(symbol->Addr, symbol->Type); update_symbol($1); $$ = symbol->Type; } else yyerror(make_yyerr("undefined", $1)); $$ = "undefined"; }
    | ID DIV_ASSIGN Expr ';'                                            { Symbol *symbol = lookup_symbol($1); if(symbol) { load(symbol); dump_code_gen("swap"); operand('/', symbol->Type); store(symbol->Addr, symbol->Type); update_symbol($1); $$ = symbol->Type; } else yyerror(make_yyerr("undefined", $1)); $$ = "undefined"; }
    | ID REM_ASSIGN Expr ';'                                            { Symbol *symbol = lookup_symbol($1); if(symbol) { load(symbol); dump_code_gen("swap"); operand('%', symbol->Type); store(symbol->Addr, symbol->Type); update_symbol($1); $$ = symbol->Type; } else yyerror(make_yyerr("undefined", $1)); $$ = "undefined"; }
    | Expr ';'                                                          { $$ = $1; }
;

FuncCall
    : ID '(' ParamsPass ')'                                             { 
                                                                            if(lookup_symbol($1)){
                                                                                Symbol *symbol = lookup_symbol($1);
                                                                                char *fun_sig = symbol->Func_sig;
                                                                                printf("call: %s%s\n", $1, fun_sig);
                                                                                $$ = symbol->Type;
                                                                            }
                                                                            else{
                                                                                yyerror(make_yyerr("undefined", $1));
                                                                                $$ = "undefined";
                                                                            }
                                                                        }
;

ParamsPass
    : Expr ',' ParamsPass
    | Expr
    |
;

VariableTypeDcl
    : ':' Type '=' Expr ';'                                             {  $$ = $2; }
    | ':' '&' STR '=' Expr ';'                                          {  $$ = "str"; }
    
    | '=' Lit ';'                                                       { $$ = $2; }
    | ':' '[' Type ';' Expr ']' '=' '[' ParamsPass ']' ';'              { $$ = "array"; }
;

Scope
    : ScopeStart DeclList ScopeEnd
;

ScopeStart
    : '{'
{
    if(!slient){
        ++scope_level;
        create_symbol();
    }
    slient = 0;
};

ScopeEnd
    : '}'
{
    dump_symbol();
    scope_level--;
};
;

%%

/* C code section */
int main(int argc, char *argv[])
{
    if (argc == 2)
    {
        yyin = fopen(argv[1], "r");
    }
    else
    {
        yyin = stdin;
    }

    yylineno = 0;
    tables = malloc(sizeof(DynamicArray **) * 4096 * 4096); //16M tables
    for(int i = 0; i < 4096 * 4096; i++) tables[i] = NULL;
    create_symbol();
    out = fopen("hw3.j", "w");
    make_out_header();
    yyparse();
    dump_symbol();
    make_out_footer();
    printf("Total lines: %d\n", yylineno);
    fclose(yyin);

    fclose(out);
    return 0;
}

static void create_symbol()
{
    DynamicArray *form = malloc(sizeof(DynamicArray *));
    dynamic_array_init(form, 10);
    printf("> Create symbol table (scope level %d)\n", scope_level);
    tables[scope_level] = form;
}

static void insert_symbol(char *name, char *type, char *fun_sig, int mut)
{
    DynamicArray *form = tables[scope_level];
    Symbol symbol;
    symbol.Func_sig = fun_sig;
    symbol.Name = name;
    symbol.Mut = mut;
    symbol.Type = type;
    symbol.Index = form->size;
    symbol.Addr = addr++;
    symbol.Lineno = yylineno + 1;

    store(symbol.Addr, type);

    printf("> Insert `%s` (addr: %d) to scope level %d\n", symbol.Name, symbol.Addr, scope_level);
    dynamic_array_append(form, symbol);
}

static struct symbol *lookup_symbol(char *name) {
    for(int i = scope_level; i >= 0; i--){
        DynamicArray *form = tables[i];

        for(int j = 0; j < form->size; j++)
            if(!strcmp(form->data[j].Name, name))
                return &form->data[j];
    }
    return NULL;
}

static void dump_symbol()
{
    printf("\n> Dump symbol table (scope level: %d)\n", scope_level);
    printf("%-10s%-10s%-10s%-10s%-10s%-10s%-10s\n",
            "Index", "Name", "Mut", "Type", "Addr", "Lineno", "Func_sig");

    DynamicArray *form = tables[scope_level];

    for (int i = 0; i < form->size; i++)
    {
        Symbol *symbol = &form->data[i];
        printf("%-10d%-10s%-10d%-10s%-10d%-10d%-10s\n", symbol->Index, symbol->Name, symbol->Mut, symbol->Type, symbol->Addr, symbol->Lineno, symbol->Func_sig);
    }

    dynamic_array_free(form);
}

static void update_symbol(char *name){
    for(int i = scope_level; i >= 0; i--){
        DynamicArray *form = tables[i];

        for(int j = 0; j < form->size; j++)
            if(!strcmp(form->data[j].Name, name))
                (&form->data[j])->Func_sig = "-";
                return;
    }
}