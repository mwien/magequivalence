##################
# To perform the experiments, run the following command (the results are written to results.ans):
# julia experiments.jl
#################

using Graphs
using DataStructures
using Random
using Statistics

function adj(D, B, a, b)
    return has_edge(D, a, b) || has_edge(D, b, a) || has_edge(B, a, b)
end

function descendants!(D, des, v)
    if !isempty(des[v])
        return des[v]
    end

    push!(des[v], v)
    
    for y in outneighbors(D, v)
        union!(des[v], descendants!(D, des, y))
    end

    return des[v]
end

function ancestors!(D, anc, v)
    if !isempty(anc[v])
        return anc[v]
    end

    push!(anc[v], v)
    
    for y in inneighbors(D, v)
        union!(anc[v], ancestors!(D, anc, y))
    end

    return anc[v]
end

function reachable(B, Z, A)
    q = Queue{Int64}()
    for v in Z
        enqueue!(q, v)
    end

    R = Set{Integer}(Z)
    
    while !isempty(q)
        x = dequeue!(q)
        for y in neighbors(B, x)
            if !(y in R) && (y in A)
                push!(R, y)
                enqueue!(q, y)
            end
        end
    end

    return R
end

function htail(D, B, anc, Z)
    A = Set{Int64}()
    for z in Z
        union!(A, anc[z])
    end
    R = reachable(B, Z, A)
    pa = Set{Int64}()
    for r in R
        for p in inneighbors(D, r)
            push!(pa, p)
        end
    end

    return setdiff(union(R, pa), Z)
end

function sibanc(D, B, anc, des, dis, C, v, w)

    A = union(anc[v], anc[w])
    DI = Set{Int64}(C[dis[v]])
    DE = union(des[v], des[w])
    SA = Set{Int64}()

    for a in A
        for b in neighbors(B, a)
            push!(SA, b)
        end
    end

    return setdiff(intersect(SA, DI), union(A, DE))
end

function csrc(D, B)
    A = Set{Tuple{Int64, Int64}}()
    VS = Set{Tuple{Int64, Int64, Int64}}()
    K = Set{Tuple{Int64, Int64}}()
    N = Set{Tuple{Int64, Int64}}()

    for y in vertices(D)
        for x in vcat(inneighbors(D, y), outneighbors(D, y), neighbors(B, y))
            if x < y
                push!(A, (x,y))
            end
        end
    end

    for y in vertices(D)
        for x in vcat(neighbors(B, y), inneighbors(D, y))
            for z in vcat(neighbors(B, y), inneighbors(D, y))
                if x < z && !adj(D, B, x, z)
                    push!(VS, (x, y, z))
                end
            end
        end
    end
    
    for y in vertices(D)
        S, mp = induced_subgraph(B, inneighbors(D, y))
        for C in connected_components(S)
            pa = Set{Int64}()
            sib = Set{Int64}()
            neigh = Set{Int64}(vcat(inneighbors(D, y), outneighbors(D, y), neighbors(B, y)))
            
            for vv in C
                d = mp[vv]
                for e in inneighbors(D, d)
                    push!(pa, e)
                end
                for e in neighbors(B, d)
                    push!(sib, e)
                end
            end

            if !isempty(setdiff(union(pa, sib), neigh))
                for b in intersect(sib, Set{Int64}(neighbors(B,y)))
                    push!(K, (b, y))
                end
            end
        end
    end

    for y in vertices(D)
        for b in inneighbors(D, y)
            push!(N, (b, y))
        end
    end
        
    return (A, VS, K, N)
end

function he(D, B)
    S = Set{Set{Int64}}()
    anc = [Set{Int64}() for i = 1:nv(D)]
    des = [Set{Int64}() for i = 1:nv(D)]
    C = connected_components(B)
    dis = zeros(Int64, nv(D))

    for i = 1:length(C)
        for v in C[i]
            dis[v] = i
        end
    end
    
    for v in vertices(D)
        for w in inneighbors(D, v)
            push!(S, Set{Int64}([v,w]))
        end

        for w in inneighbors(D, v)
            for z in inneighbors(D, v)
                if z != w && !adj(D, B, z, w)
                    push!(S, Set{Int64}([v,w,z]))
                end
            end
        end

        ancestors!(D, anc, v)
        descendants!(D, des, v)
    end

    for v in vertices(B)
        for w in neighbors(B, v)
            if v > w
                continue
            end
            push!(S, Set{Int64}([v, w]))
            T = htail(D, B, anc, Set{Int64}([v, w]))
            for z in T
                if !(adj(D, B, v, z) && adj(D, B, w, z))
                    push!(S, Set{Int64}([v, w, z]))
                end
            end

            for z in sibanc(D, B, anc, des, dis, C, v, w)
                if !(adj(D, B, v, z) && adj(D, B, w, z))
                    if z in reachable(B, v, union(anc[v], union(anc[w], anc[z])))
                        push!(S, Set{Int64}([v, w, z]))
                    end
                end
            end
        end
    end
    return S
end

function convert(D, B)
    DM = SimpleDiGraph(nv(D))
    BM = SimpleGraph(nv(B))

    anc = [Set{Int64}() for i = 1:nv(D)]

    for y in vertices(D)
        ancestors!(D, anc, y)
    end
    
    for y in vertices(D)
        for w in htail(D, B, anc, Set{Int64}(y))
            add_edge!(DM, w, y)
        end
    end
    

    for C in connected_components(B)
        for u in C
            for v in C
                if u == v || u in anc[v] || v in anc[u]
                    continue
                end
                if u in reachable(B, v, union(anc[u], anc[v]))
                    add_edge!(BM, u, v)
                end
            end
        end
    end

    return(DM, BM)
end 

function generate_graph(n, d)
    D = SimpleDiGraph(n)
    B = SimpleGraph(n)

    ecount = 0
    while ecount < d*n
        a = rand(1:n)
        b = rand(1:n)

        if b < a
            tmp = a
            a = b
            b = tmp
        end

        if a != b && !has_edge(D, a, b) && !has_edge(B, a, b)
            if rand(1:2) == 1
                add_edge!(D, a, b)
            else
                add_edge!(B, a, b)
            end
            ecount += 1
        end
    end

    perm = randperm(n)
    return D[perm], B[perm]
end

function experiments()
    Random.seed!(1234)
    outfile = open("results.ans", "a")
    println("Results are written to 'results.ans'. Below, only the progress is shown.")
    for d in ["3", "10"] # "3"
        if d == "3"
             nve = [250, 500, 750, 1000, 1250, 1500, 1750, 2000]
        else
            nve = [25, 50, 75, 100, 125, 150, 175, 200]
        end
        global n = 0
        for x in nve
            n = x
            println("Computing for n=" * string(n) * " and k=" * d * "n")
            hetime = []
            csrctime = []
            dirprev = []
            bidirprev = []
            ratprev = []
            dir = []
            bidir = []
            rat = []
            for rep = 1:250
                D, B = generate_graph(n, eval(Meta.parse(d)))
                push!(dirprev, ne(D))
                push!(bidirprev, ne(B))
                push!(ratprev, ne(D) / ne(B))
                D, B = convert(D, B)
                push!(dir, ne(D))
                push!(bidir, ne(B))
                push!(rat, ne(D) / ne(B))
                push!(hetime, @elapsed(he(D, B)))
                push!(csrctime, @elapsed(csrc(D, B)))
            end
            println(outfile, "Number of vertices: " * string(n) * " d: " * d)
            println(outfile, "  ADMG #DIR: " * string(mean(dirprev)) * ", ADMG #BIDIR: " * string(mean(bidirprev)) * ", ADMG #RATIO: " * string(mean(ratprev)))
            println(outfile, "  MAG #DIR: " * string(mean(dir)) * ", MAG #BIDIR: " * string(mean(bidir)) * ", MAG #RATIO: " * string(mean(rat)))
            println(outfile, "  HE avg time in s: " * string(mean(hetime)))
            println(outfile, "  HE std dev: " * string(std(hetime)))
            println(outfile, "  C-SRC avg time in s: " * string(mean(csrctime)))
            println(outfile, "  C-SRC std dev: " * string(std(csrctime)))
            flush(outfile)
        end
    end
end

function readgraph(file = stdin)
    if file != stdin
        infile = open(file, "r")
    else
        infile = stdin
    end
    (n, d, b) = parse.(Int, split(readline(infile)))
    readline(infile)
    D = SimpleDiGraph(n)
    for i = 1:d
        (x, y) = parse.(Int, split(readline(infile)))
        add_edge!(D, x, y)
    end
    B = SimpleGraph(n)
    for i = 1:b
        (x, y) = parse.(Int, split(readline(infile)))
        add_edge!(B, x, y)
    end
    if file != stdin
        close(infile)
    end
    return (D, B)
end

experiments()
