// Modelo Circuito Euleriano num grafo não-orientado e ligado

var sig Leader in Node {}

var sig Node {
    var adj : set Node
}

// Algumas das propriedades desejadas para o sistema

assert noMoreThenOneLeader {
    always (one Leader)
}

// Especifique as condições iniciais do sistema

fact Init {
    all n: Node | n.adj in Node-n
    all n1, n2: Node | n1 in n2.adj implies n2 in n1.adj
    all n: Node | Node in n.^adj
    all n: Node | rem[#n.adj, 2] = 0
    one Leader
    all n: Node | Node-n in n.adj
    #Node = 5
}


pred removeArc [n1, n2: Node] {
    // guard
    Leader = n1
    #n1.adj > 1
    n1 in n2.adj
    n2 in n1.adj

    //efects
    n1.adj' = n1.adj-n2
    n2.adj' = n2.adj-n1
    Leader' = n2    

    //frame condition
    all n: Node-(n1+n2) | n.adj' = n.adj
    all n: Node | Node in n.^adj'
}

pred removeBridge [n1, n2: Node] {
    // guard
    Leader = n1
    #n1.adj = 1
    n1 in n2.adj
    n2 in n1.adj

    //efects
    n1.adj' = n1.adj-n2
    n2.adj' = n2.adj-n1
    Leader' = n2

    //frame condition
    all n: Node-(n1+n2) | n.adj' = n.adj
}

pred nop {
    Node' = Node
    adj' = adj
    Leader' = Leader
}

pred end [n : Node]{
    // guard
    Leader = n

    //efects
    #n.adj = 0
    
    //frame condition
    Leader' = none
    Node' = Node
    adj' = adj
}

fact Traces {
    always (nop or some n1, n2: Node | removeArc[n1 , n2]
                or some n1, n2: Node | removeBridge[n1 , n2]
	            or some n1: Node | end[n1])
}

run Exemplo {
    eventually (all n: Node | no n.adj and n not in Leader)
    
} for 5 Node, 20 steps
