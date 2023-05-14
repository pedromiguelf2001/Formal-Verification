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
    edge_labels = []
    
    for edge in cfa:
        (body, trans) = cfa[edge] 
        for i in range(len(trans)):
            (dest, cond) = trans[i]
            edges.append([edge,dest])
    for edge in edges:
        (body, trans) = cfa[edge[0]]
        for i in range(len(trans)):
            (dest, cond) = trans[i]
            if(dest == edge[1]):
                #edge_labels[(edge[0],edge[1])] = cond
                edge_labels.append((edge[0], edge[1], {'w':cond}))
        #print("teste",trans)
        #edge_labels[(edge[0],edge[1])] = 
        #print(edge)
    print(edge_labels)

    return cfa



desenha(cfa)
