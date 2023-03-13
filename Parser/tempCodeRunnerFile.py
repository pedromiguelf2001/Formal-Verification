cfa = {
    "init": (
        "x = 5; y = 4; z = 0;",
        [("switch", "")]
    ),
    "switch": (
        "",
        [("isEven", "y != 0 && (y % 2) == 0"), ("isOdd", "y != 0 && (y % 2) != 0"), ("end", "y == 0")]
    ),
    "isEven": (
        "x = 2 * x; y = y / 2;",
        [("switch", "")]
    ),
    "isOdd": (
        "y = y - 1; z = z + x;",
        [("switch", "")]
    ),
    "end": (
        "",
        [("end", "")]
    )
}

def desenha(cfa):
    edges = []
    for edge in cfa:
        print("edge:", edge)
        (body, trans) = cfa[edge] 
        print("trans", trans)
        (dest, cond) = trans[0]
        for dest in trans[0]:
            print("dest", dest)
            edges.append([edge, dest])
    print(edges)

    return cfa



desenha(cfa)
