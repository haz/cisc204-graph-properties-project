
import sys

from bauhaus import Encoding, proposition, constraint, Or, And
from bauhaus.utils import count_solutions, likelihood

# These two lines make sure a faster SAT solver is used.
from nnf import config
config.sat_backend = "kissat"

NUM_NODES = int(sys.argv[1])

# Encoding that will store all of your constraints
E = Encoding()

class Hashable:
    def __hash__(self):
        return hash(str(self))

    def __eq__(self, __value: object) -> bool:
        return hash(self) == hash(__value)

    def __repr__(self):
        return str(self)

# To create propositions, create classes for them first, annotated with "@proposition" and the Encoding
@proposition(E)
class Edge(Hashable):

    def __init__(self, x, y):
        self.x = x
        self.y = y

    def __str__(self):
        return f"({self.x} -> {self.y})"

@proposition(E)
class Adjacent(Hashable):
    def __init__(self, x, y):
        self.x = x
        self.y = y
    def __str__(self):
        return f"({self.x} (-) {self.y})"

@proposition(E)
class Distance(Hashable):

    def __init__(self, x, y, n) -> None:
        self.x = x
        self.y = y
        self.n = n

    def __str__(self) -> str:
        return f"d({self.x}, {self.y}) = {self.n}"

# Create the propositions

all_edges = []
all_adjacent = []
for n1 in range(NUM_NODES):
    for n2 in range(NUM_NODES):
        all_edges.append(Edge(f'n{n1}', f'n{n2}'))
        all_adjacent.append(Adjacent(f'n{n1}', f'n{n2}'))

all_distances = []
for edge in all_edges:
    for d in range(NUM_NODES+1):
        all_distances.append(Distance(edge.x, edge.y, d))


# TODO: Force the graph to be disconnected
#  - new vars x
#  - x0 holds
#  - for everything adjacent, one implies the other
#  - there's some x that doesn't hold
def force_disconnected():
    return

def example_graph(version):
    assert NUM_NODES == 4, f"Asked for a custom graph of 4 nodes, but instead used {NUM_NODES} as a parameter."

    desired_edges = {
        1: {(0,1), (1,2), (2,0), (2,3), (3,1)}
    }

    for n1 in range(NUM_NODES):
        for n2 in range(NUM_NODES):
            if (n1, n2) in desired_edges[version]:
                E.add_constraint(Edge(f'n{n1}', f'n{n2}'))
            else:
                E.add_constraint(~Edge(f'n{n1}', f'n{n2}'))



def build_theory():

    # I don't want self loops in my theory
    for node in range(NUM_NODES):
        E.add_constraint(~Edge(f'n{node}', f'n{node}'))

    # Define edges being adjacent
    for edge in all_edges:
        x,y = edge.x, edge.y
        # If an edge, then it's adjacent
        E.add_constraint(edge >> Adjacent(x, y))
        # Adjacent is symmetric
        E.add_constraint(Adjacent(x, y) >> Adjacent(y, x))
        # Adjacent means an edge exists in one of the directions
        E.add_constraint(Adjacent(x, y) >> (Edge(x, y) | Edge(y, x)))

    # A node is distance 0 to itself
    for node in range(NUM_NODES):
        E.add_constraint(Distance(f'n{node}', f'n{node}', 0))

    # Nodes that are connected, have a distance of 1
    for edge in all_edges:
        dprop = Distance(edge.x, edge.y, 1)
        E.add_constraint(edge >> dprop)

    # Distance is transitive
    # If d(n1,n2,d1) and d(n2,n3,d2), then d(n1,n3,d3=d1+d2)
    for n1 in range(NUM_NODES):
        for n2 in range(NUM_NODES):
            for n3 in range(NUM_NODES):
                for d1 in range(NUM_NODES+1):
                    for d2 in range(NUM_NODES+1):
                        for d3 in range(NUM_NODES+1):
                            if d3 == d1+d2:
                                E.add_constraint(
                                    (Distance(f'n{n1}',f'n{n2}',d1) & Distance(f'n{n2}',f'n{n3}',d2))
                                        >>
                                    Distance(f'n{n1}',f'n{n3}',d3)
                                )



    # Distance is well supported
    # If d(n1,n3,d), then there should be some n2 such that d(n1,n2,d-1)
    # BUG: This constraint causes all distances to become true
    for n1 in range(NUM_NODES):
        for n2 in range(NUM_NODES):
            for d in range(1, NUM_NODES+1):
                predecessors = []
                for n3 in range(NUM_NODES):
                    predecessors.append(Edge(f'n{n2}', f'n{n3}') & Distance(f'n{n1}', f'n{n2}', d-1))
                E.add_constraint(Distance(f'n{n1}', f'n{n2}', d) >> Or(predecessors))


    # Get all of the propositions in there
    for edge in all_edges:
        E.add_constraint(edge | ~edge)


    example_graph(1)

    return E


def print_graph(sol):

    print("\tAdjacency List:")
    for n1 in range(NUM_NODES):
        out = f"\t  n{n1}:"
        for n2 in range(NUM_NODES):
            if sol[Edge(f'n{n1}', f'n{n2}')]:
                out += f" n{n2}"
        print(out)

    print("\n\tDistances:")
    for d in range(NUM_NODES+1):
        out = f"\t  d={d}: "
        res = []
        for n1 in range(NUM_NODES):
            for n2 in range(NUM_NODES):
                if sol[Distance(f'n{n1}', f'n{n2}', d)]:
                    res.append(str((n1, n2)))
        out += ", ".join(res)
        print(out)

if __name__ == "__main__":

    T = build_theory()
    # Don't compile until you're finished adding all your constraints!
    T = T.compile()
    # After compilation (and only after), you can check some of the properties
    # of your model:
    print("\nSatisfiable: %s" % T.satisfiable())
    # print("# Solutions: %d" % count_solutions(T))
    # print("   Solution: %s" % T.solve())

    print("    Solution:")
    sol = T.solve()
    print_graph(sol)

    # print("\nVariable likelihoods:")
    # for v,vn in zip([e1,e2,e3], ["e1", "e2", "e3"]):
    #     # Ensure that you only send these functions NNF formulas
    #     # Literals are compiled to NNF here
    #     print(" %s: %.2f" % (vn, likelihood(T, v)))
    print()
