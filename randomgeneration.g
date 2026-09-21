# Generates a random n x n partial matrix with density parameter p in [0, 1].
# Each slot [i][j] has probability p of being populated with a random pair [a, b].
RandomPartialMatrix := function(n, p)
    local T, i, j, a, b, threshold;
    T := List([1..n], i -> List([1..n], j -> []));
    
    # Convert float boundary p * 1000 to an integer
    threshold := Int(p * 1000);
    
    for i in [1..n] do
        for j in [1..n] do
            if Random([1..1000]) <= threshold then
                a := Random([1..n]);
                b := Random([1..n]);
                T[i][j] := [a, b];
            fi;
        od;
    od;
    return T;
end;;


# Generates a random PARTIAL INJECTIVE matrix (higher chance of defining a partial action).
# Ensured by assigning distinct targets to distinct domain pairs.
RandomPartialInjectiveMatrix := function(n, p)
    local T, domain, targets, count, num_entries, idx_dom, idx_tgt, pair_dom, pair_tgt;
    
    T := List([1..n], i -> List([1..n], j -> []));
    domain := Tuples([1..n], 2);
    targets := ShallowCopy(domain);
    
    # Calculate how many cells to populate based on density p
    num_entries := Int(p * n^2);
    
    for count in [1..num_entries] do
        if Length(domain) = 0 then break; fi;
        
        # Pick a random unused domain cell and pair it with a random unused target
        idx_dom := Random([1..Length(domain)]);
        idx_tgt := Random([1..Length(targets)]);
        
        pair_dom := domain[idx_dom];
        pair_tgt := targets[idx_tgt];
        
        T[pair_dom[1]][pair_dom[2]] := pair_tgt;
        
        Remove(domain, idx_dom);
        Remove(targets, idx_tgt);
    od;
    
    return T;
end;;


# Searches for valid partial B_3 solutions by sampling random partial injective matrices.
FindRandomB3PartialActionSolutions := function(n, p, max_attempts)
    local attempt, T, valid_solutions;
    valid_solutions := [];
    
    Print("Searching for valid B_3 partial action solutions (n = ", n, ", density = ", p, ")...\n");
    
    for attempt in [1..max_attempts] do
        T := RandomPartialInjectiveMatrix(n, p);
        
        if IsB3PartialActionSolution(T, n) then
            Print("Found valid solution at attempt #", attempt, "!\n");
            Add(valid_solutions, T);
        fi;
    od;
    
    Print("Found ", Length(valid_solutions), " valid solution(s) out of ", max_attempts, " attempts.\n");
    return valid_solutions;
end;;





#==============================================================
# Generating Random Partial Subsolution of a Global Solution
#==============================================================



# Generates a partial subsolution from a known global solution T_global.
# 
# Parameters:
#   T_global : an m x m matrix representing a known YB solution
#   m        : full size of T_global
#   n        : target subset size (n <= m)
#   p        : probability in [0, 1] of setting a remaining cell to []
#
# Returns:
#   A new n x n partial matrix whose underlying set is re-indexed to {1..n}
RandomPartialSubsolution := function(T_global, m, n, p)
    local kept_indices, index_map, T_sub, i, j, orig_i, orig_j, target, a, b, threshold;

    if n > m then
        Error("Subsolution size n (", n, ") cannot exceed global size m (", m, ")!");
    fi;

    threshold := Int(p * 1000);

    kept_indices := Combinations([1..m], n)[Random([1..Binomial(m, n)])];
    
    index_map := [];
    for i in [1..n] do
        index_map[kept_indices[i]] := i;
    od;

    T_sub := List([1..n], i -> List([1..n], j -> []));

    for i in [1..n] do
        orig_i := kept_indices[i];
        for j in [1..n] do
            orig_j := kept_indices[j];
            target := T_global[orig_i][orig_j];

            if IsBound(index_map[target[1]]) and IsBound(index_map[target[2]]) then
                # Entry is kept only if the random roll exceeds the drop threshold
                if Random([1..1000]) > threshold then
                    a := index_map[target[1]];
                    b := index_map[target[2]];
                    T_sub[i][j] := [a, b];
                fi;
            fi;
        od;
    od;

    return T_sub;
end;;


# Samples random subsolutions from a list of known global solutions
SamplePartialSubsolutions := function(DB, m, n, p, max_samples)
    local sample, T_global, T_partial, valid_sols;

    valid_sols := [];
    Print("Sampling partial subsolutions (subset size n = ", n, ", p = ", p, ")...\n");

    for sample in [1..max_samples] do
        # Pick a random global solution from your database
        T_global := Random(DB);
        
        # Generate a partial subsolution
        T_partial := RandomPartialSubsolution(T_global, m, n, p);

        # Verify if it satisfies the partial action axioms for B_3
        if IsB3PartialActionSolution(T_partial, n) then
            Print("Found valid partial action subsolution at sample #", sample, "!\n");
            Add(valid_sols, T_partial);
        fi;
    od;

    Print("Found ", Length(valid_sols), " valid partial action solution(s) out of ", max_samples, " samples.\n");
    return valid_sols;
end;;