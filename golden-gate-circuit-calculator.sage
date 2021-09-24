################################################################################################################

#ALGORITHMS

################################################################################################################


###RANDOMISED ALGORITHM###



def randomised(a,p,l,A):
    #a is alpha, p is prime, l is length, A is the A value
    #randomised finds x1 and x2

    #Determine value of xi1, xi2 from alpha
    xi1 = (a*p^(l/2)).real()
    xi2 = (a*p^(l/2)).imag()

    #Randomly choose k_1, k_2 up to l^2A times, each time we test if they satisfy the wanted conditions
    X=["error","error"]
    for n in [1..ceil(l^(2*A))]:
        k1 = randrange(0,floor(l^A))
        k2 = randrange(0,floor(l^A))
        x1 = floor(xi1) - k1
        x2 = floor(xi2) - k2
        RHS = p^l-(x1)^2-(x2)^2
        if ((RHS in Primes()) and mod(RHS,4)==1):
            X=[x1,x2]
            break

    #Returns "error" if no x1,x2 found
    return X


###HERMITE AND SCHOOF ALGORITHM###

def Hermite(N):

    #SCHOOF

    #N must be prime==1 mod 4

    #Want to determine sqaure roots of -1 mod N with N==1 mod 4, so we take x^2=-1 in Schoof
    #For Quadratic fields -1 is not discriminant of complex quadratic field, so we must multiply by 4 to get -4 (discrim of Q(sqrt(-1)))
    #So must divide by 2 at end and use x=-4 in Schoof

    #For x=-4 we find E: Y^2=X^3-X, so A=0,B=-1 where y^2=x^3+A*x+B
    k = GF(N)
    E = EllipticCurve(k, [0,0,0,-1,0])
    t=(N+1)-E.cardinality()
    #We now solve the Frobenius equation phi^2-t*phi+q=0. We also define a and b from phi=(a+b*sqrt(x))/2
    a=t
    #divide by 2 as we used in the beginning x=-4
    b=(sqrt(-t^2+4*N))/2
    #this x is now the solution to x^2=-1 mod N
    x0=(a/(2*b))
    #We now find the equivalent of the fraction in mod N
    x0=mod(x0,N)


    #IMPROVED HERMITE

    #Euclidean algorithm on N/x0, in general we take n=q*m+r
    n=N
    #x0 defined by mod equation it is stuck in field F_p, so int converts it out to be an integer
    m=int(x0)

    #We now calculate the remainders (stored in R) of the euclidean algorithm until we have one <sqrt(N)
    r=sqrt(N)
    R=[]
    while r>=sqrt(N):
        r=n%m
        n=m
        m=r
        R.append(r)
        #adds last r to list
        if r<sqrt(N):
            r=n%m
            n=m
            m=r
            R.append(r)

    #This sets x3 and x4 as the last two elements of R
    if R[0]>1:
        [x3,x4]=[R[-1],R[-2]]
    else:
        [x3,x4]=[int(x0),1]

    #Returns values of x3 and x4
    return [x3,x4]


###NAVIGATION ALGORITHM###

def navigation(M,l,p):

    #We work in the field CC (complex numbers)
    F=CC

    #We define our golden gate set S- here we took the v-gates for p=5
    s1=matrix(F,2,[1+2*I,0,0,1-2*I])
    s2=matrix(F,2,[1,2,-2,1])
    s3=matrix(F,2,[1,2*I,2*I,1])
    S=[s1,s2,s3]

    #We determine 'mu' and 'delta' elements from S, and from this generate our cayley graph
    mu=[]
    delta=[]
    for s in S:
        if s^2==-p:
            delta.append(s)
        else:
            mu.append(s)

    #We create a regular tree and span out from v_0 using known S elements, add labels up to length l and then find our solution at length l and work backwards

    #We create a function to find total number of vertices upto and including level k for a p-regular tree
    def N(k,p):
        return (p^(k+1)-1)//(p-1)

    #We define nS to be the number of generators from S (nS=p+1)
    nS=p+1
    #We define n to be the total number of vertices
    n=N(l,nS)

    #We create a graph g with n vertices and no edges
    g=Graph(n)
    #We also create a list that holds the place of the matrices corresponding to the graph vertices
    G=[1]*n

    #Create generating set gS of S with inverses for mu and deltas
    gS=S
    for m in mu:
        #This is the equivalent of taking the conjugate on quaternions (taking tranpose)
        gS.append((m.conjugate()).transpose())

    #k1 is level
    for k1 in [0..l-1]:
        #k2 is place in level
        for k2 in [1..nS^k1]:
            #c is edge number from the starting vertex
            for c in [1..nS]:

                #g calculations
                #place of first vertex
                v1=N(k1-1,nS)+(k2-1)
                #place of second vertex
                v2=v1*nS+c
                g.add_edge(v1,v2)

                #G calculations
                G[v2]=G[v1]*gS[(c-1)]

    #Now want to find our diophantine solution for p^l on the tree and compare to points on level l wrt quotient of units
    #Then we can run a shortest path algorithm to the centre

    #Units U
    u1=matrix(F,2,[1,0,0,1])
    u2=matrix(F,2,[-1,0,0,-1])
    u3=matrix(F,2,[I,0,0,-I])
    u4=matrix(F,2,[-I,0,0,I])
    u5=matrix(F,2,[0,1,-1,0])
    u6=matrix(F,2,[0,-1,1,0])
    u7=matrix(F,2,[0,I,I,0])
    u8=matrix(F,2,[0,-I,-I,0])
    U=[u1,u2,u3,u4,u5,u6,u7,u8]

    #We find the combinations of M with the unitary matrices
    MU=[M*u for u in U]
    #We test to see which element of MU is in the tree at level l
    for k3 in [(N(l-1,nS)+1)..(N(l-1,nS)+1+(nS^l))]:
        if G[k3] in MU:
            #v is the label for our matrix M on the tree
            v=k3
            break


    #We find the shortest path and output the order of elements combine together to make it
    V=(list(g.shortest_simple_paths(0,v)))[0]
    #Create edge set of path
    E=[]
    for k in [0..(len(V)-2)]:
        E.append([V[k],V[k+1]])
    #Draw out path visually
    if l<=2:
        plot=g.show(vertex_colors={'orange':V}, edge_colors={'blue':E}, tree_root=0)
    else:
        plot=0

    #We now find the generators of the shortest path (L1 - positions in S, L2 - elements of S)

    #L1 is the list of POSITIONS of element in S used to generate M
    #We do this by finidng the remainder when dividing by nS, this relates to how we formed the regular tree
    L1=[]
    V.remove(0)
    for k in V:
        #m (final definition) is the position in S
        m=k%nS
        if m==0:
            m=nS-1
        else:
            m=m-1
        L1.append(m)

    #G[v] is matrix equivalent to label v on tree
    #L2 is list of ELEMENTS in S
    L2=[]
    L2=[gS[k] for k in L1]

    #This is unitary used in sequence (take inverse as we find M*u=seq, so M=seq*u^(-1))
    u=(U[MU.index(G[v])])^(-1)

    #We return the plot. generating set and unitray matrix used
    return plot,L2,u



################################################################################################################

#MAIN

################################################################################################################

def main(a,L,maxA):

    #As we have used V-gates we set p=5
    p=5


    #RANDOMISED

    #alpha=a+b*i
    #We run the randomised alogorithm for each l upto each maxA
    x1="error"
    x2="error"
    for l in [1..L]:
        l0=l
        for A in [1.01,1.02..(maxA)]:
            A0=A
            [x1,x2]=randomised(a,p,l,A)
            if x1!="error":
                break
        if x1!="error":
            #Takes out of circuit when we find x1 and x2
            break

    #This outputs error if we find no solution
    if x1=="error":
        return "error","error","error","error","error","error","error"


    #HERMITE AND SCHOOF

    N=p^l0-x1^2-x2^2
    [x3,x4]=Hermite(N)


    #NAVIGATION

    M=matrix(CC,2,[x1+x2*I,x3+x4*I,-x3+x4*I,x1-x2*I])
    [plot,L2,u] = navigation(M,l0,p)


    #OUTPUT

    #We create some outputs for the display to reduce the number of return items from the main function
    o1="New input matrix (normalised and then multiplied by" ,p^(l0/2) ,"(p^{length/2})): " ,matrix(CC,2,[a*p^(l0/2),0,0,a.conjugate()*p^(l0/2)])
    o2="Diophantine Approximation: ", M
    o3="Circuit of Golden Gates: ",L2
    o4="Unitary matrix used: ", u
    o5="Value of A used: " , float(A0)
    return o1,o2,o3,o4,o5,l0,plot



################################################################################################################

#DISPLAY

################################################################################################################


#POTENTIALLY NORMALISE BY NORMALISING GATE SET? OR CAN MULTIPLY INPUT BY 5^(l/2) AT THE END


html("<h1>Golden Gate Circuit Calculator (V-gates)</h1>")
html("<h4>We take an input of a+bi to create an input matrix [a+bi, 0][0, a-bi].</h4>")
html("<h4>We find that our Diophantine approximation = Product(Golden gate circuit)* unitary matrix used.</h4>")

@interact
def display(a = input_box(1, label='a: '), b = input_box(1, label='b: '), L=slider([1..10], label="Maximum Length"), Amax=slider([1.01,1.02..2], label="Maximum A: ") ):

    #INPUT

    a0=a/sqrt(a^2+b^2)
    b0=b/sqrt(a^2+b^2)
    [o1,o2,o3,o4,o5,l0,plot]=main(a0+b0*i,L,Amax)

    #OUTPUT

    if o1=="error":
        print("No Solution was found for the current inputs. Either resubmit current inputs (randomised algorithm used) or try increasing the maximum length and A values.")
    else:
        if plot==0:
            html("<h5>GRAPH PLOT ONLY AVAILABLE FOR LENGTH < 3</h5>")
        pretty_print("Input matrix: ", matrix(CC,2,[a+b*I,0,0,a-b*I]))
        pretty_print(o1[0], o1[1], o1[2], o1[3])
        pretty_print(o2[0], o2[1])
        pretty_print(o3[0],o3[1])
        pretty_print(o4[0], o4[1])
        pretty_print("Length: ", l0)
        pretty_print(o5[0], o5[1])
        p=5
        pretty_print("Maximum error in Diophantine Approximation: ", (2*l0^(Amax/2))*p^(l0/4).numerical_approx(digits=10))
