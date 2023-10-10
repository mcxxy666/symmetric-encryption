
%{
  open Datatype
%}

%token <string> IDENT
%token <int> INT
%token INL
%token INR
%token IN
%token ZERO
%token OUTPUT
%token INPUT
%token OUTPUTS
%token INPUTS
%token PAR
%token NU
%token NUS
%token NUSYM
%token NUASYM
%token CHECK
%token CASE
%token DECRYPT
%token SPLIT
%token MATCH
%token BEGIN
%token END
%token IS
%token LPAREN
%token RPAREN
%token ELPAREN
%token ERPAREN
%token COLON
%token COMMA
%token PERIOD
%token WITH
%token COPY
%token UNIT
%token EOF

%left PAR
%left COMMA
%nonassoc PERIOD

%start main
%type <unit Datatype.procexp> main
%type <Datatype.message> mes

%%

main:
  proc EOF
  { $1 }

proc:
  ZERO
  { Zero }
| mes OUTPUT mes
  { Out($1,$3) }
| mes INPUT IDENT
  { In($1,$3,(),Zero) }
| mes INPUT IDENT PERIOD proc
  { In($1,$3,(),$5) }
| mes OUTPUTS mes
  { OutS($1,$3) }
| mes INPUTS IDENT
  { InS($1,$3,(),Zero) }
| mes INPUTS IDENT PERIOD proc
  { InS($1,$3,(),$5) }
| proc PAR proc
  { Par($1,$3) }  
| LPAREN NU IDENT RPAREN proc
  { Nu($3,(),$5) }
| LPAREN NUS IDENT RPAREN proc
  { NuS($3,(),$5) }
| LPAREN NUSYM IDENT RPAREN proc
  { NuSym($3,(),$5) }
| LPAREN NUASYM IDENT COMMA IDENT RPAREN proc
  { NuAsym($3,(),$5,(),$7) }
| CHECK IDENT IS IDENT IN proc
  { Check($2,$4,$6) }
| DECRYPT mes IS ELPAREN IDENT ERPAREN mes IN proc
  { DecSym($2,$5,(),$7,$9) }
| DECRYPT mes IS ELPAREN ELPAREN IDENT ERPAREN ERPAREN mes IN proc
  { DecAsym($2,$6,(),$9,$11) }
| CASE mes IS INL LPAREN IDENT RPAREN PERIOD proc IS INR LPAREN IDENT RPAREN PERIOD proc
  { Case($2,$6,(),$9,$13,(),$16) }
| SPLIT mes IS LPAREN IDENT COMMA IDENT RPAREN IN proc
  { Split($2,$5,(),$7,(),$10) }
| MATCH mes IS LPAREN IDENT COMMA IDENT RPAREN IN proc
  { Match($2,$5,$7,(),$10) }
| BEGIN mes PERIOD proc
  { Begin($2,$4) }
| END mes 
  { End($2) }
| COPY proc
  { Copy($2) }
| LPAREN proc RPAREN
  { $2 }
;

mes:
  IDENT
  { Name(ENname($1)) }
| UNIT
  { Unit }
| LPAREN mes COMMA mes RPAREN
  { Pair($2,$4) }
| INL LPAREN mes RPAREN
  { Inl($3) }
| INR LPAREN mes RPAREN
  { Inr($3) }
| ELPAREN mes ERPAREN mes
  { EncSym($2,$4) }
| ELPAREN ELPAREN mes ERPAREN ERPAREN mes
  { EncAsym($3,$6) }
| LPAREN mes RPAREN
  { $2 }
;
