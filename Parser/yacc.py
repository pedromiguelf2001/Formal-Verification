from lexer import LexerPySMT
import ast
import ply.yacc as yacc
import sys

# ---------------- Programa Simples----------------
class ParserPySMT(object):
    def __init__(self):
        self.arith_map = {
            "+": "BVAdd",
            "-": "BVSub",
            "*": "BVMul",
            "/": "BVDiv",
            "%": "BVURem",
        }
        self.precedence = (
            ('left', 'SUM', 'SUB'),
            ('left', 'MULT', 'DIV', 'MOD'),
        )
        self.tokens = LexerPySMT.tokens
        self.lexer = LexerPySMT()
        self.parser = yacc.yacc(start="ExpressionInit", module=self)
    
    def compile(self, code):
        self.parser.PySMT = ""
        self.parser.parse(code, lexer=self.lexer.lexer)
        return self.parser.PySMT

    def p_Expression_Init(self, p):
        "ExpressionInit : Atribs"
        self.parser.PySMT = f"{p[1]}"

    def p_Atribs(self, p):
        """Atribs : Atrib ';'
                | Atribs Atrib ';'"""
        if len(p) == 3:
            p[0] = f"{p[1]}"
        else:
            p[0] = f"And({p[1]},{p[2]})"
        
    def p_Atrib(self, p):
        """Atrib : ID ATRIB Expre"""
        p[0] = f"Equals(prox['{p[1]}'], {p[3]})"

    def p_Expre(self, p):
        """Expre : Expre SUM Expre
                | Expre SUB Expre
                | Expre MULT Expre
                | Expre DIV Expre
                | Expre MOD Expre"""
        p[0] = f"{self.arith_map[p[2]]}({p[1]}, {p[3]})"

    def p_Expre_Paren(self, p):
        """Expre : LParen Expre RParen"""
        p[0] = f"({p[2]})"

    def p_Expre_ID(self, p):
        """Expre : ID"""
        p[0] = f"curr['{p[1]}']"

    def p_Expre_NUM(self, p):
        """Expre : NUM"""
        p[0] = f"BV({p[1]}, 16)"

    def p_error(self, p):
        print('Syntax error!\np -> ', p)
        self.parser.sucesso = False


with open(f"tests/{sys.argv[1]}.txt") as f:
    content = f.read()

text = ParserPySMT().compile(content)

print(text)

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