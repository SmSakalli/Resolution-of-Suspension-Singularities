
A<x,y> := AffineSpace(Rationals(),2);

// ______________input________________

curve := x^5-y^2;

// k is the degree of t, for Nemethi's Algorithm 
// range of k
start  := 10;
finish := 1000;

// period of the graphs
num    := 10;
// ___________________________________




//_____________Subordinate Functions_______________

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


C := Curve(A,curve);
res_graph:= ResolutionGraph(C,Origin(A));


g:= UnderlyingGraph(res_graph);
V:= Vertices(g);
E:= Edges(g);

m_list := Multiplicities(res_graph);
arrow_list:= TransverseIntersections(res_graph);
size:=#arrow_list;

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
    
neighbours := [ InNeighbours(V[i]) join OutNeighbours(V[i]) : i in [1..size] ];
neighbours := neighbours cat [ InNeighbours(V[i]) join OutNeighbours(V[i]) : i in [size+1..#V] ];

original_vertices:= [1..#V];  
E := Edges(g);
s_list := [ #n : n in neighbours ];
d_list := [ GCD([m_list[i]] cat [m_list[Index(v)] : v in neighbours[i]]) : i in [1..#V] ];



arrow_vertices:= [v:v in [size+1..#V]];


//______________________________________________________


Get_Resolution_Graph := function(k)

    neighbours := [ InNeighbours(V[i]) join OutNeighbours(V[i]) : i in [1..size] ];
    neighbours := neighbours cat [ InNeighbours(V[i]) join OutNeighbours(V[i]) : i in [size+1..#V] ];
    
    genus:=[];
    for i in [1..#V] do
        sum:=0;
        for n in neighbours[i] do
            sum +:= GCD(GCD(m_list[i],m_list[Index(n)]),k);
        end for;
        gen:=((2-s_list[i])*GCD(m_list[i],k)+sum)/(GCD(d_list[i],k));
        Append(~genus, (2-gen)/2);
    end for;

    vertex_number := [];
    for i in [1..size] do
        num := GCD(d_list[i], k);
        Append(~vertex_number, Integers()!num);
    end for;
    for i in [size+1..#V] do
        Append(~vertex_number, 1);
    end for;

    new_mult := [];
    for i in [1..size] do
        mult := m_list[i] div GCD(m_list[i], k);
        Append(~new_mult, Integers()!mult);
    end for;
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


    internal_vertices_sol := [];
    internal_vertices_mult :=[];
    important_iv_multiplicities := [];

    for i in [1..#E] do
        u := m_list[Index(InitialVertex(E[i]))] div edge_number[i];
        v := m_list[Index(TerminalVertex(E[i]))] div edge_number[i];
        a := k div edge_number[i];
        
        sol := string_type_solution(u, v, a);
        
        if sol eq -1 then
            print "Error Occurred";
        else
            if sol eq 0 then
                Append(~internal_vertices_sol, []);
                Append(~internal_vertices_mult, []);
                Append(~important_iv_multiplicities, []);
            else
                c := GCD(Integers()!u, Integers()!a);
                a := a div c;
                u := u div c;

                decom := fraction_decom(a / sol);
                Append(~internal_vertices_sol, decom);

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

            end if;
        end if;
    end for;



    neighbours := neighbours cat [ InNeighbours(V[i]) join OutNeighbours(V[i]) : i in [size+1..#V] ];


    new_intersections := [];
    for i in [1..#V] do
        n_summation := 0;
        for j in neighbours[i] do
            check:= 0;
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



    // Reindexing the original vertices and finding the order of the graph
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


    //_________________________________New Graph_____________________

    //Updating new label lists
    G_mult   := [];   // multiplicities
    G_selfi  := [];   // self-intersections
    G_genus  := [];   // genus
    G_arrow_vertices := [orig_vertex_start[i]:i in arrow_vertices];     // arrow vertices
        // Vertex copies
    for i in [1..#V] do
        for c in [1..vertex_number[i]] do
            Append(~G_mult,  new_mult[i]);
            Append(~G_selfi, new_intersections[i]);
            Append(~G_genus, genus[i]);
        end for;
    end for;

        // Internal vertices along edges
    for e in [1..#E] do
        n_iv := #internal_vertices_mult[e];
        for c in [1..edge_number[e]] do
            for p in [1..n_iv] do
                Append(~G_mult,  internal_vertices_mult[e][p]);
                // Self-intersection of an internal vertex = internal_vertices_sol[e][p]
                Append(~G_selfi, internal_vertices_sol[e][p]);
                Append(~G_genus, 0);
            end for;
        end for;
    end for;


    // Create the new graph, which is a multigraph
    G := MultiGraph< total_G | >;
    VG := Vertices(G);  


    // Adding edges

    for e_idx in [1..#E] do
        u_orig := Index(InitialVertex(E[e_idx]));
        v_orig := Index(TerminalVertex(E[e_idx]));

        en   := edge_number[e_idx];
        vnu  := vertex_number[u_orig];
        vnv  := vertex_number[v_orig];
        n_iv := #internal_vertices_mult[e_idx];

        eu := en div vnu;
        ev := en div vnv;

        u_base  := orig_vertex_start[u_orig];
        v_base  := orig_vertex_start[v_orig];
        iv_base := edge_iv_start[e_idx];

        for cu in [0..vnu-1] do
            for local_ec in [0..eu-1] do
                ec := cu * eu + local_ec;
                cv := ec mod vnv;

                G_u := u_base + cu;
                G_v := v_base + cv;

                if n_iv eq 0 then
                    AddEdge(~G, VG[G_u], VG[G_v]);
                else
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


// _______________________ BLOW DOWN  _______________________________


H_mult   := G_mult;
H_selfi  := G_selfi;
H_genus  := G_genus;
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


// Loop to eliminate (-1)-rational curves until no change is possible.

repeat
    changed := false;

    // ---------- degree 1 ----------
    deg_1_list := [];
    for v in Alldeg(H,1) do
        if H_selfi[Index(v)] eq -1 and
           H_genus[Index(v)] eq 0 then
            Append(~deg_1_list,Index(v));
        end if;
    end for;

    counter := #deg_1_list;
    if counter gt 0 then
        changed := true;
    end if;

    while counter gt 0 do
        i := deg_1_list[counter];

        if H_selfi[i] eq -1 and H_genus[i] eq 0 then

            nbr := GetNeighbours(i,H_edges)[1];
            H_selfi[nbr] +:= 1;

            reindex := [j lt i select j else j-1 : j in [1..total_H]];

            H_mult   := [H_mult[j]   : j in [1..total_H] | j ne i];
            H_selfi  := [H_selfi[j]  : j in [1..total_H] | j ne i];
            H_genus  := [H_genus[j]  : j in [1..total_H] | j ne i];

            H_edges := [[reindex[e[1]],reindex[e[2]]]
                        : e in H_edges
                        | not (e[1] eq i or e[2] eq i)];

             H_arrow_vertices :=
            [
               reindex[j] :
               j in H_arrow_vertices |
               j ne i
            ];

            deg_1_list := [j : j in deg_1_list | j ne i];
            deg_1_list := [reindex[j] : j in deg_1_list];

            total_H -:= 1;
        end if;

        counter -:= 1;
    end while;

    if changed then
        H := MultiGraph< total_H | >;
        VH := Vertices(H);
        for e in H_edges do
            AddEdge(~H,VH[e[1]],VH[e[2]]);
        end for;

        continue;
    end if;

    // ---------- degree 2 ----------
    deg_2_list := [];
    for v in Alldeg(H,2) do
        if H_selfi[Index(v)] eq -1 and
           H_genus[Index(v)] eq 0 then
            Append(~deg_2_list,Index(v));
        end if;
    end for;

    counter := #deg_2_list;
    if counter gt 0 then
        changed := true;
    end if;

    while counter gt 0 do
        i := deg_2_list[counter];

        nbrs := GetNeighbours(i,H_edges);

        if #nbrs eq 2 and
           H_selfi[i] eq -1 and
           H_genus[i] eq 0 then

            nbr1 := nbrs[1];
            nbr2 := nbrs[2];

            H_selfi[nbr1] +:= 1;
            H_selfi[nbr2] +:= 1;

            reindex := [j lt i select j else j-1 : j in [1..total_H]];

            H_mult   := [H_mult[j]   : j in [1..total_H] | j ne i];
            H_selfi  := [H_selfi[j]  : j in [1..total_H] | j ne i];
            H_genus  := [H_genus[j]  : j in [1..total_H] | j ne i];

            H_edges := [[reindex[e[1]],reindex[e[2]]]
                        : e in H_edges
                        | not (e[1] eq i or e[2] eq i)];

            Append(~H_edges,[reindex[nbr1],reindex[nbr2]]);

            H_arrow_vertices :=
            [
               reindex[j] :
               j in H_arrow_vertices |
               j ne i
            ];

            deg_2_list := [j : j in deg_2_list | j ne i];
            deg_2_list := [reindex[j] : j in deg_2_list];

            total_H -:= 1;
        end if;

        counter -:= 1;
    end while;

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

    return [* H, H_mult, H_selfi, H_genus, H_arrow_vertices, total_H *];
end function; 

SubdivideMultigraph := function(multigraph, mult_list, self_list, genus_list, arrow_list)
    E := Edges(multigraph);
    n := #Vertices(multigraph);
    G  := Graph< n | >;
    VG := Vertices(G);

    // Label original vertices
    for i in [1..n] do
        l := [mult_list[i], self_list[i], genus_list[i], 0];
        AssignLabel(~G, VG[i], l);
    end for;

    seen_pairs := [];
    w := n;
    for i in [1..#E] do
        u    := Index(InitialVertex(E[i]));
        v    := Index(TerminalVertex(E[i]));
        pair := [Minimum(u,v), Maximum(u,v)];
        if pair in seen_pairs then
            w +:= 1;
            AddVertex(~G);
            VG := Vertices(G);
            AssignLabel(~G, VG[w], [0, 0, 0, -1]);
            AddEdge(~G, VG[u], VG[w]);
            AddEdge(~G, VG[w], VG[v]);
        else
            Append(~seen_pairs, pair);
            AddEdge(~G, VG[u], VG[v]);
        end if;
    end for;

    return G;
end function;




// _______________________ ISOMORPHISM CHECK  _______________________________


first_round := [];
for i in [1..num] do
    res := Get_Resolution_Graph(i);
    first_round[(i-1) mod num + 1] :=
        SubdivideMultigraph(res[1], res[2], res[3], res[4], res[5]);
    print "saving graph for k=", i;
end for;

isom_check:=true;
for i in [num+1..finish] do
    iso:= false;
    res:=Get_Resolution_Graph(i);
    res:=SubdivideMultigraph(res[1],res[2],res[3],res[4],res[5]);

    original := ((i-1) mod num) + 1;
    if IsIsomorphic(res, first_round[original]) then
        iso:= true;
    else
        isom_check:=false;
    end if;
    print "Checking reduced graph for k=", i, ": ", iso;
end for; 

if isom_check then
    print "\nIsomorphisms HOLD for all k in [", start, "..", finish, "] with period", num;
else
    print "\nIsomorphisms FAIL — see mismatches above";
end if;

