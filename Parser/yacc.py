from lexer import lexer, LexerPySMT
import ast
import ply.yacc as yacc
import sys

# ---------------- Programa Simples----------------
def p_Expression_Init(p):
    "ExpressionInit : Atribs"
    parser.PySMT = f"{p[1]}"

def p_Atribs(p):
    """Atribs : Atrib ';'
              | Atribs Atrib ';'"""
    if len(p) == 3:
        p[0] = f'{p[1]}{p[2]}'
    else:
        p[0] = f'{p[1]}'
    
def p_Atrib(p):
    """Atrib : ID ATRIB Expre"""
    p[0] = f'Equals(prox[\'{p[1]}\'], {p[3]})'

arith_map = {
    "+": "BVAdd",
    "-": "BVSub",
    "*": "BVMul",
    "/": "BVDiv",
    "%": "BVURem",
}

def p_Expre(p):
    """Expre : Expre SUM Expre
             | Expre SUB Expre
             | Expre MULT Expre
             | Expre DIV Expre
             | Expre MOD Expre"""
    p[0] = f'{arith_map[p[2]]}( {p[1]}, {p[3]} )'

def p_Expre_ID(p):
    """Expre : ID"""
    p[0] = f'curr[\'{p[1]}\']'

def p_Expre_NUM(p):
    """Expre : NUM"""
    p[0] = f'BV({p[1]}, 16)'



# ---------------- Programa Mais Avançado----------------
'''
def p_Cond(p):
    """Cond : Cond OR Expre
            | Cond AND Expre
            | Cond EQ Expre
            | Cond NEQ Expre
            | Cond GT Expre
            | Cond LT Expre
            | Cond GEQ Expre
            | Cond LEQ Expre"""
    p[0] = f'{condition_map[p[2]]}( {p[1]}, {p[3]} )'

condition_map ={
    "||": "Or\n",
    "&&": "And\n",
    "==": "EqualsOrIff\n",
    "!=": "NotEquals\n",
    ">": "BVUGT\n",
    "<": "BVULT\n",
    ">=": "BVUGE\n",
    "<=": "BVULE\n",
}
'''
def p_error(p):
    print('Syntax error!\np -> ', p)
    parser.sucesso = False

tokens = LexerPySMT.tokens
lexer = LexerPySMT()
parser = yacc.yacc(start="ExpressionInit")

parser.PySMT = ""

with open(f"tests/{sys.argv[1]}.txt") as f:
    content = f.read()
 

lexer.input(content)
parser.parse(lexer=lexer.lexer)

print(parser.PySMT)