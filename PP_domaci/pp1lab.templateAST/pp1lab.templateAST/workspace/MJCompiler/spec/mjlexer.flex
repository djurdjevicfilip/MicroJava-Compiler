package rs.ac.bg.etf.pp1;
import org.apache.log4j.*;
import java_cup.runtime.*;
%%

%{
	private Logger log = Logger.getLogger(getClass());

	public int getLine() {
		return yyline;
	}
	
	public int getColumnn() {
		return yycolumn;
	}
	
	public Symbol getSymbol(int type, Object value){
		return new Symbol(type, getLine() + 1, getColumnn() + 1, value);
	}
%}

%function next_token
%type java_cup.runtime.Symbol

%state COMMENT

// na kraju fajla vrati EOF
%eofval{
return new Symbol(sym.EOF);
%eofval}

%cup
%line
%column

%%
<COMMENT> {
 "\r\n" {yybegin(YYINITIAL);}
 . {yybegin(COMMENT);}
}
<YYINITIAL> {
" " {}
"\b" {}
"\t" {}
"\r\n" {}
"\f" {}
"true" | "false" {return getSymbol (sym.BOOL, yytext());}
";" {return getSymbol(sym.SEMI, yytext());}
"=" {return getSymbol(sym.ASSIGN, yytext());}
"++" {return getSymbol(sym.INC, yytext());}
"--" {return getSymbol(sym.DEC, yytext());}
"(" {return getSymbol(sym.LPAREN, yytext());}
")" {return getSymbol(sym.RPAREN, yytext());}
"read" {return getSymbol(sym.READ, yytext());}
"print" {return getSymbol(sym.PRINT, yytext());}
"," {return getSymbol(sym.COMMA, yytext());}
"new" {return getSymbol(sym.NEW, yytext());}
">" {return getSymbol(sym.GREATER, yytext());}
"==" {return getSymbol(sym.EQUAL, yytext());}
"<" {return getSymbol(sym.LESS, yytext());}
">=" {return getSymbol(sym.GREATER_OR_EQUAL, yytext());}
"<=" {return getSymbol(sym.LESS_OR_EQUAL, yytext());}
"!=" {return getSymbol(sym.NOT_EQUAL, yytext());}
"+" {return getSymbol(sym.PLUS, yytext());}
"-" {return getSymbol(sym.MINUS, yytext());}
"*" {return getSymbol(sym.MULT, yytext());}
"/" {return getSymbol(sym.DIVIDE, yytext());}
"%" {return getSymbol(sym.MOD, yytext());}
"[" {return getSymbol(sym.LBRACKET, yytext());}
"]" {return getSymbol(sym.RBRACKET, yytext());}
"if" {return getSymbol(sym.IF, yytext());}
"else" {return getSymbol(sym.ELSE, yytext());}
"do" {return getSymbol(sym.DO, yytext());}
"while" {return getSymbol(sym.WHILE, yytext());}
"break" {return getSymbol(sym.BREAK, yytext());}
"continue" {return getSymbol(sym.CONTINUE, yytext());}
"program" { return getSymbol(sym.PROG, yytext());}
"const" { return getSymbol(sym.CONST, yytext());}
"void" { return getSymbol(sym.VOID, yytext());}
"return" {return getSymbol(sym.RETURN, yytext());}
"{" {return getSymbol(sym.LBRACE, yytext());}
"}" {return getSymbol(sym.RBRACE, yytext());}
"||" {return getSymbol(sym.OR, yytext());}
"&&" {return getSymbol(sym.AND, yytext());}
":" {return getSymbol(sym.COLON, yytext());}

"case" {return getSymbol(sym.CASE, yytext());}
"class" {return getSymbol(sym.CLASS, yytext());}
"?" {return getSymbol(sym.QUESTION_MARK, yytext());}
"." {return getSymbol(sym.DOT, yytext());}
"switch" {return getSymbol(sym.SWITCH, yytext());}
"enum" {return getSymbol(sym.ENUM, yytext());}
"extends" {return getSymbol(sym.EXTENDS, yytext());}

"//" {yybegin(COMMENT);}
([a-z]|[A-Z])[a-z|A-Z|0-9|_]* {return getSymbol(sym.IDENT, yytext());}
[0-9]+ {return getSymbol(sym.NUMBER, new Integer(yytext()));}
"'"."'" {return getSymbol(sym.CHAR_CONST, new Character(yytext().charAt(1)));}
"~"|"!"|"?"|"^"|"$"|"#"|"&"|"|"|([0-9]+[a-z|A-Z|_])|"'"|":"|"@"|"\\" {log.error("Leksicka greska za simbol \"" + yytext() + "\" na liniji " + (getLine() + 1) + ", koloni " + (getColumnn() + 1) + "!");}

}