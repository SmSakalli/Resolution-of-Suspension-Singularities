A<x,y> := AffineSpace(Rationals(),2);


// ______________input________________

//Input the value for the power of t:
k := 3;
//Input a polynomial in terms of x and y (and k if needed):
curve := -x^5+y^2;

// ___________________________________


printf "Data for equation %o and parameter k=%o\n\n", curve, k;


//_____________Subordinate Functions_______________

// For integers u,v and a  with gcd(u,v,a) = 1,
    // string_type_solution() finds the (unique) solution to the equation
    //
    //      v + x*(u/gcd(u,a)) ≡ 0 (mod a/gcd(u,a))
    //
string_type_solution := function(u, v, a)
    u := Integers()!u;
    v := Integers()!v;
    a := Integers()!a;
    c := GCD(Integers()!u, Integers()!a);
    u := u div c;
    a := a div c;
    if a eq 1 then
        return 0;
    end if;
    for i in [0..a-1] do
        w:= Integers()! (v + i*u);
        if (w mod a) eq 0 then
            return i;
        end if;
    end for;

    return -1;
end function;

// For any rational number m, fraction_decom() returns the list of 
// coeffiencts in its (negative) continued fraction decomposition
fraction_decom := function(m)
    if Floor(m) eq m then
        return [-Integers()!m];
    end if;

    a := [];
    whole := false;
    current_m := m;

    while not whole do
        val := Floor(current_m);
        Append(~a, -val - 1);
        current_m := -(1 / (current_m - val - 1));

        if current_m eq Floor(current_m) then
            Append(~a, -Integers()!current_m);
            whole := true;
        end if;
    end while;

    return a;
end function;

// _______________________ RESOLUTION GRAPH (NON-REDUCED) _______________________________

// Read off the curve from input.
// Build resolution graph and read the underlying graph. 
// Save multiplicities and number of transverse intersections of the corresponding exceptional
//component with the strict transform of the curve.
C := Curve(A,curve);
res_graph:= ResolutionGraph(C,Origin(A));

g:= UnderlyingGraph(res_graph);
V:= Vertices(g);
E:= Edges(g);

m_list := Multiplicities(res_graph);
arrow_list:= TransverseIntersections(res_graph);
size:=#arrow_list;

// Add one "arrow" vertex for each transverse intersection of
// an exceptional component with the strict transform, attached
// to the corresponding exceptional-component vertex.
// Each arrow vertex has multiplicity 1.
for i in [1..#arrow_list] do
    if arrow_list[i] gt 0 then
        for j in [1..arrow_list[i]] do
            AddVertex(~g);
            V:= Vertices(g);
            AddEdge(~g, V[i], V[#V]);
            V:= Vertices(g);
            Append(~m_list, [1]);
        end for;
    end if;
end for;
    
// Neighbours of every vertex (original vertices, then arrow vertices)
neighbours := [ InNeighbours(V[i]) join OutNeighbours(V[i]) : i in [1..size] ];
neighbours := neighbours cat [ InNeighbours(V[i]) join OutNeighbours(V[i]) : i in [size+1..#V] ];

original_vertices:= [1..#V];  
E := Edges(g); //reset to the updated edges
// Degrees of each vertex.
s_list := [ #n : n in neighbours ];
// GCD of multiplicities of each vertex with its neighbours.
d_list := [ GCD([m_list[i]] cat [m_list[Index(v)] : v in neighbours[i]]) : i in [1..#V] ];

// Genus of each vertex as given by equation (a) in (1), Apendix 1.
genus:=[];
for i in [1..#V] do
    sum:=0;
    for n in neighbours[i] do
        sum +:= GCD(GCD(m_list[i],m_list[Index(n)]),k);
    end for;
    gen:=((2-s_list[i])*GCD(m_list[i],k)+sum)/(GCD(d_list[i],k));
    Append(~genus, (2-gen)/2);
end for;

// print information
print "The initial resolution graph: ";
g;
arrow_vertices:= [v:v in [size+1..#V]];
printf "Vertices %o are arrows.\n", arrow_vertices;
printf "The genus of each vertex is %o. \n", genus;
print "";




// ==================================================================
// To build the NEW GRAPH, G: 
//      - make certain number of copies of each vertex
//      - compute new multiplicities, selfintersections and genus
//      - make certain number of copies of each edge
//      - find number, multiplicity, and selfintersection of 
//        internal vertices required along each edge.
//
// Data used to build G:
//   vertex_number                     - number of copies of each original vertex
//   new_multiplicities                - multiplicity of the copies
//   new_selfintersections             - self-intersection of the copies
//   genus                             - genus of the original vertices
//   edge_number                       - number of copies of each string
//   internal_vertices_mult            - multiplicities along each edge
//   internal_vertices_sol             - self-intersections along each edge
// ==================================================================
vertex_number := [];
for i in [1..size] do
    num := GCD(d_list[i], k);
    Append(~vertex_number, Integers()!num);
end for;
// Arrow vertices always have a single copy.
for i in [size+1..#V] do
    Append(~vertex_number, 1);
end for;

new_mult := [];
for i in [1..size] do
    mult := m_list[i] div GCD(m_list[i], k);
    Append(~new_mult, Integers()!mult);
end for;
// Arrow vertices always have a multiplicity 1.
for i in [size+1..#V] do
    Append(~new_mult, 1);
end for;

edge_number := [];
for i in [1..#E] do
    u_idx := Index(InitialVertex(E[i]));
    v_idx := Index(TerminalVertex(E[i]));
    strings := GCD([m_list[u_idx], m_list[v_idx], k]);
    Append(~edge_number, strings);
end for;

internal_vertices_sol := []; // self-intersections of internal vertices, indexed per edge
internal_vertices_mult :=[]; // multiplicities of internal vertices, indexed per edge
important_iv_multiplicities := []; // [first, last] internal-vertex multiplicity, indexed per edge


// For each edge [v_1,v_2], the appropriate set of internal vertices is found.
    // Each element of internal_vertex_sol is a list of integers
    //     [k_1,...,k_s]
    // that corresponds to the selfintersections of the new vericies iv_1,...,iv_s.
    // In the new graph, each copy of edge [v_1,v_2] is replaced by an chain of edges
    //     [v_1,iv_1], [iv_1,iv_2], ..., [iv_s,v_2]
    // It constitutes STEP 1 in (1), Apendix 1. 
for i in [1..#E] do
    u := m_list[Index(InitialVertex(E[i]))] div edge_number[i];
    v := m_list[Index(TerminalVertex(E[i]))] div edge_number[i];
    a := k div edge_number[i];
    
    sol := string_type_solution(u, v, a);
    
    if sol eq -1 then
        print "Error Occurred";
    else
        if sol eq 0 then
            // No internal vertices needed along this edge
            Append(~internal_vertices_sol, []);
            Append(~internal_vertices_mult, []);
            Append(~important_iv_multiplicities, []);
            printf "Edge %o has %o copies and no internal vertices.\n", E[i], 
edge_number[i];
        else
            c := GCD(Integers()!u, Integers()!a);
            a := a div c;
            u := u div c;

            decom := fraction_decom(a / sol);
            Append(~internal_vertices_sol, decom);

            printf "Edge %o has %o copies and internal vertices with intersections (oriented):\n %o\n", 
                   E[i], edge_number[i], decom;


            // Find the multiplicities along the chain of internal vertices.
            m :=[];
            
            m1 := (v + (u * sol)) div a;
            Append(~m, m1);


            if #decom eq 1 then
                Append(~important_iv_multiplicities, [m1, m1]);
            else
                m2 := (-decom[1] * m1) - u;
                Append(~m, m2);
                if #decom eq 2 then
                    Append(~important_iv_multiplicities, [m1, m2]);
                else
                    x := m1;
                    y := m2;
                    mj := 0;
                    for j in [3..#decom] do
                        mj := (-decom[j-1] * y) - x;
                        Append(~m, mj);
                        x := y;
                        y := mj;
                    end for;
                    Append(~important_iv_multiplicities, [m1, y]);
                end if;
            end if;

            Append(~internal_vertices_mult, m);
            printf "and multiplicities (oriented):\n %o\n", m;
            print "";

        end if;
    end if;
end for;

// Re-include neighbour data for the arrow vertices (kept as in the
// original derivation, needed for the self-intersection pass below).
neighbours := neighbours cat [ InNeighbours(V[i]) join OutNeighbours(V[i]) : 
i in [size+1..#V] ];

new_intersections := [];
for i in [1..#V] do
    n_summation := 0;
    for j in neighbours[i] do

        //Fist: find correct orientation of edge stored.
        check:= 0; // 1: edge points i -> j, 2: edge points j -> i
        for e in E do
            if [Index(InitialVertex(e)),Index(TerminalVertex(e))] eq [i,Index(j)] then
                check:= 1;
                edge:= e;
                break;
            end if;
            if [Index(InitialVertex(e)),Index(TerminalVertex(e))] eq [Index(j),i] then
                check:= 2;
                edge:= e;
                break;
            end if;
        end for;

        // Second:add appropriate factor to n_summation.
        if check eq 1 then
            idx := Index(E, edge);
            if #internal_vertices_sol[idx] eq 0 then
                n_summation +:= new_mult[Index(j)] * edge_number[idx];
            else
                n_summation +:= important_iv_multiplicities[idx][1] * edge_number[idx];
            end if;
        elif check eq 2 then
            idx := Index(E ,edge);
            if #internal_vertices_sol[idx] eq 0 then
                n_summation +:= new_mult[Index(j)] * edge_number[idx];
            else
                n_summation +:= important_iv_multiplicities[idx][2] * edge_number[idx];
            end if;
        end if;
    end for;

    Append(~new_intersections, -n_summation div (new_mult[i] * vertex_number[i]));
end for;

printf "\nThe number of new vertices for vertices: %o\n", vertex_number;
printf "With respective self-intersections: %o\n", new_intersections;
printf "And respective multiplicities: %o\n", new_mult;

//==================================================================
// All data has been gathered.
// Next, is to build the Multigraph G
//==================================================================

// Reindex the original vertices and finding the order of the graph.
// Assign a contiguous block of indices in G to each original vertex's
// copies, followed by blocks for each edge's internal vertices.

total_G := 0;
orig_vertex_start := [];
for i in [1..#V] do
    Append(~orig_vertex_start, total_G + 1);
    total_G +:= vertex_number[i];
end for;

G_original_vertices:= [1..total_G];

edge_iv_start := [];
for e in [1..#E] do
    Append(~edge_iv_start, total_G + 1);
    total_G +:= edge_number[e] * #internal_vertices_mult[e];
end for;

//Updating new label lists
G_mult   := [];   // multiplicities
G_selfi  := [];   // self-intersections
G_origin := [];   // human-readable label of each vertex's origin, for testing
G_genus  := [];   // genus
G_arrow_vertices := [orig_vertex_start[i]:i in arrow_vertices];    // arrow vertices (reindexed)

// Add data for vertex copies 
for i in [1..#V] do
    for c in [1..vertex_number[i]] do
        Append(~G_mult,  new_mult[i]);
        Append(~G_selfi, new_intersections[i]);
        Append(~G_genus, genus[i]);
        Append(~G_origin, Sprintf("v%o_copy%o", i, c));
    end for;
end for;

// Add data for internal vertices introduced along each edge's copies
for e in [1..#E] do
    n_iv := #internal_vertices_mult[e];
    for c in [1..edge_number[e]] do
        for p in [1..n_iv] do
            Append(~G_mult,  internal_vertices_mult[e][p]);
            Append(~G_selfi, internal_vertices_sol[e][p]);
            // All internal vertices have genus 0.
            Append(~G_genus, 0);
            Append(~G_origin, Sprintf("edge%o_copy%o_iv%o", e, c, p));
        end for;
    end for;
end for;

// Build the multigraph itself
G := MultiGraph< total_G | >;
VG := Vertices(G);  

// For each original edge, add its copies in the new graph G,
// distributing them cyclically among the copies of its endpoints and
// threading each copy through its chain of internal vertices (if any).
for e_idx in [1..#E] do
    u_orig := Index(InitialVertex(E[e_idx]));
    v_orig := Index(TerminalVertex(E[e_idx]));

    copies_of_edge := edge_number[e_idx];
    copies_of_u    := vertex_number[u_orig];
    copies_of_v    := vertex_number[v_orig];
    n_iv           := #internal_vertices_mult[e_idx];

    // How many edge-copies attach to each copy of u (resp. v)
    edges_per_u_copy := copies_of_edge div copies_of_u;

    // Starting index in G of each block: u's copies, v's copies, and    // this edge's internal vertices
    u_base  := orig_vertex_start[u_orig];
    v_base  := orig_vertex_start[v_orig];
    iv_base := edge_iv_start[e_idx];

    // Distribute the edge-copies cyclically.
    for copy_u in [0..copies_of_u-1] do
        for local_ec in [0..edges_per_u_copy-1] do
            ec := copy_u * edges_per_u_copy + local_ec;
            copy_v := ec mod copies_of_v;

            G_u := u_base + copy_u;
            G_v := v_base + copy_v;

            if n_iv eq 0 then
                // No internal vertices: connect the endpoints directly
                AddEdge(~G, VG[G_u], VG[G_v]);
            else
                // Thread the edge-copy through its chain of internal vertices
                iv_start := iv_base + ec * n_iv;

                AddEdge(~G, VG[G_u], VG[iv_start]);
                for p in [1..n_iv-1] do
                    AddEdge(~G, VG[iv_start + p - 1], VG[iv_start + p]);
                end for;
                AddEdge(~G, VG[iv_start + n_iv - 1], VG[G_v]);
            end if;
        end for;
    end for;
end for;

//==================================================================
// Blowdown of (-1)-rational curves of degree 1 or 2 in G:
//==================================================================

// Save all data to be trimmed
H_mult   := G_mult;
H_selfi  := G_selfi;
H_genus  := G_genus;
H_origin := G_origin;
H_arrow_vertices:=G_arrow_vertices;
H_original_vertices:=G_original_vertices;

EG := Edges(G);
H_edges := [[Index(InitialVertex(EG[i])), Index(TerminalVertex(EG[i]))] : i in [1..#EG]];
total_H := total_G;

H := MultiGraph< total_H | >;
VH := Vertices(H);
for e in H_edges do AddEdge(~H, VH[e[1]], VH[e[2]]); end for;

GetNeighbours := function(u,edge_list)
  return [e[1] eq u select e[2] else e[1] : e in edge_list | e[1] eq u or e[2] eq u];
end function;

//Added for parallel edges. If a degree two (−1)-sphere appears at the end of a multigraph and is 
//connected to the same vertex by two parallel edges, do not blow it down.
HasParallelEdges := function(u,edge_list)
    nbrs := [e[1] eq u select e[2] else e[1] :
             e in edge_list | e[1] eq u or e[2] eq u];

    return #nbrs ne #Setseq(SequenceToSet(nbrs));
end function;

// Loop to eliminate (-1)-rational curves until no change is possible.
repeat
    changed := false;

    // ---------- degree 1 ----------
    // Store all leaves of the graph with selfintersection -1 and genus 0.
    deg_1_list := [];
    for v in Alldeg(H,1) do
        if H_selfi[Index(v)] eq -1 and
           H_genus[Index(v)] eq 0 and
           not (Index(v) in H_arrow_vertices) then
            Append(~deg_1_list,Index(v));
        end if;
    end for;

    //If any are found, then the loop will have to repeat.
    counter := #deg_1_list;
    if counter gt 0 then
        changed := true;
    end if;

    // Eliminate all (-1)-leaves.
    while counter gt 0 do
        i := deg_1_list[counter];

        // Re-check that the remaining candidates satisfy the requirements
        // after having blown down some vertices in the list.
        
           nbrs := GetNeighbours(i,H_edges);

           if #nbrs eq 1 and
           H_selfi[i] eq -1 and
           H_genus[i] eq 0 and
           not (i in H_arrow_vertices) and
           not HasParallelEdges(i,H_edges) then
            // Increase the selfintersection value by +1 to all of its neighbours. 
            nbr := nbrs[1];
            H_selfi[nbr] +:= 1;

            // Reindex: old vertex i is removed, rest shift down by 1
            reindex := [j lt i select j else j-1 : j in [1..total_H]];

            H_mult   := [H_mult[j]   : j in [1..total_H] | j ne i];
            H_selfi  := [H_selfi[j]  : j in [1..total_H] | j ne i];
            H_genus  := [H_genus[j]  : j in [1..total_H] | j ne i];
            H_origin := [H_origin[j] : j in [1..total_H] | j ne i];

            H_edges := [[reindex[e[1]],reindex[e[2]]]
                         : e in H_edges | e[1] ne i and e[2] ne i];

            H_arrow_vertices := [j : j in H_arrow_vertices | j ne i];
            H_arrow_vertices := [reindex[j] : j in H_arrow_vertices];


            // Delete i from the list and decrease number of total vertex of H.
            deg_1_list := [j : j in deg_1_list | j ne i];
            deg_1_list := [reindex[j] : j in deg_1_list];

            total_H -:= 1;

        end if;

        counter -:= 1;
    end while;

    // If any (-1)-leaves were found, we rebuild the graph and go back to the beginning.
    if changed then
        H := MultiGraph< total_H | >;
        VH := Vertices(H);
        for e in H_edges do
            AddEdge(~H,VH[e[1]],VH[e[2]]);
        end for;

        continue;
    end if;

    // ---------- degree 2 ----------
    // In case that no (-1)-leaves are found, we search for all degree 2 vertices 
    // with selfintersection -1, genus 0 and that are not arrows.
    // (No other degree vertex  can be deleted without breaking the graph structure.)
    deg_2_list := [];
    for v in Alldeg(H,2) do
        if H_selfi[Index(v)] eq -1 and
           H_genus[Index(v)] eq 0 and
           not HasParallelEdges(Index(v),H_edges) and
           not (Index(v) in H_arrow_vertices) then
            Append(~deg_2_list,Index(v));
        end if;
    end for;

    //If any are found, then the loop will have to repeat.
    counter := #deg_2_list;
    if counter gt 0 then
        changed := true;
    end if;

    // Eliminate all degree 2 (-1)-rational curves.
    while counter gt 0 do
        i := deg_2_list[counter];

        // Re-check that the remaining candidates satisfy the requirements
        // after having blown down some vertices in the list.
        nbrs := GetNeighbours(i,H_edges);

        if #nbrs eq 2 and
           H_selfi[i] eq -1 and
           H_genus[i] eq 0 and
           not (i in H_arrow_vertices) and
           not HasParallelEdges(i,H_edges)then

            // Increase the selfintersection value by +1 to all of its neighbours. 
            nbr1 := nbrs[1];
            nbr2 := nbrs[2];

            H_selfi[nbr1] +:= 1;
            H_selfi[nbr2] +:= 1;

            // Reindex: old vertex i is removed, rest shift down by 1
            reindex := [j lt i select j else j-1 : j in [1..total_H]];

            H_mult   := [H_mult[j]   : j in [1..total_H] | j ne i];
            H_selfi  := [H_selfi[j]  : j in [1..total_H] | j ne i];
            H_genus  := [H_genus[j]  : j in [1..total_H] | j ne i];
            H_origin := [H_origin[j] : j in [1..total_H] | j ne i];

            H_edges := [[reindex[e[1]],reindex[e[2]]]
                         : e in H_edges | e[1] ne i and e[2] ne i];

            Append(~H_edges,[reindex[nbr1],reindex[nbr2]]);

            H_arrow_vertices := [j : j in H_arrow_vertices | j ne i];
            H_arrow_vertices := [reindex[j] : j in H_arrow_vertices];

            // Delete i from the list and decrease number of total vertex of H.
            deg_2_list := [j : j in deg_2_list | j ne i];
            deg_2_list := [reindex[j] : j in deg_2_list];

            total_H -:= 1;
        end if;

        counter -:= 1;
    end while;

    // If any degree 2 (-1)-rational curves were found, 
    // we rebuild the graph and go back to the beginning.
    if changed then
        H := MultiGraph< total_H | >;
        VH := Vertices(H);
        for e in H_edges do
            AddEdge(~H,VH[e[1]],VH[e[2]]);
        end for;

        continue;
    end if;

until not changed;


// Rebuild final graph only once
H := MultiGraph< total_H | >;
VH := Vertices(H);

for e in H_edges do
    AddEdge(~H,VH[e[1]],VH[e[2]]);
end for;

print "\n=== MultiGraph H ===";
printf "\nTotal vertices in MultiGraph H: %o\n", total_H;


// _______________________ EXPORT TO SAGE _______________________________
printf "\n Copy the following into SageMath to produce the REDUCED GRAPH \n";

// Vertex labels
printf "vertex_mult = {";
for i in [1..total_H] do
    if i lt total_H then
        printf "%o: %o, ", i-1, H_mult[i];
    else
        printf "%o: %o", i-1, H_mult[i];
    end if;
end for;
printf "}\n";

printf "vertex_selfi = {";
for i in [1..total_H] do
    if i lt total_H then
        printf "%o: %o, ", i-1, H_selfi[i];
    else
        printf "%o: %o", i-1, H_selfi[i];
    end if;
end for;
printf "}\n";

printf "vertex_genus = {";
for i in [1..total_H] do
    if i lt total_H then
        printf "%o: %o, ", i-1, H_genus[i];
    else
        printf "%o: %o", i-1, H_genus[i];
    end if;
end for;
printf "}\n";

// Edge list
printf "edge_list = [";
EG := Edges(H);
for i in [1..#EG] do
    if i lt #EG then
        printf "(%o,%o), ", Index(InitialVertex(EG[i]))-1, Index(TerminalVertex(EG[i]))-1;
    else
        printf "(%o,%o)", Index(InitialVertex(EG[i]))-1, Index(TerminalVertex(EG[i]))-1;
    end if;
end for;
printf "]\n";

//Decorations
printf "arrow_vertices = [";
for i in [1..#H_arrow_vertices] do
    if i lt #H_arrow_vertices then
        printf "%o, ", H_arrow_vertices[i]-1;
    else
        printf "%o", H_arrow_vertices[i]-1;
    end if;
end for;
printf "]\n";