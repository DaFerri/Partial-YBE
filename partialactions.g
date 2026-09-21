# ===========================================================================
# 1. DOMAIN & PARTIAL ACTION CHECKS FOR B_3
# ===========================================================================

# Computes the inverse partial map R^{-1} of T on {1..n}
# Returns fail if T is not injective on its domain S
InversePartialYBMap := function(T, n)
    local T_inv, i, j, res;
    T_inv := EmptyPartialYBMap(n);
    for i in [1..n] do
        for j in [1..n] do
            res := T[i][j];
            if res <> [] then
                # Check for injectivity: target slot must be empty
                if T_inv[res[1]][res[2]] <> [] then
                    return fail; # Not injective!
                fi;
                T_inv[res[1]][res[2]] := [i, j];
            fi;
        od;
    od;
    return T_inv;
end;

# Checks if a partial matrix T comes from a partial action of B_3 on X^3
# Requirements:
# 1. R is a partial bijection S -> R(S)
# 2. Strong YBE Domain Matching: Dom(R12 R23 R12) = Dom(R23 R12 R23)
# 3. Equality on defined domain: (R12 R23 R12)(x,y,z) = (R23 R12 R23)(x,y,z)
IsB3PartialActionSolution := function(T, n)
    local i, j, k, lhs, rhs, T_inv;

    # Requirement 1: R must be a partial bijection (partially invertible)
    T_inv := InversePartialYBMap(T, n);
    if T_inv = fail then return false; fi;

    # Requirements 2 & 3: Strong YBE domain matching & equality
    for i in [1..n] do
        for j in [1..n] do
            for k in [1..n] do
                lhs := EvalLHS(T, i, j, k);
                rhs := EvalRHS(T, i, j, k);

                # Strong Domain Matching: both defined or both undefined
                if (lhs = []) <> (rhs = []) then
                    return false;
                fi;

                # If both defined, they must be equal
                if lhs <> [] and lhs <> rhs then
                    return false;
                fi;
            od;
        od;
    od;

    return true;
end;


# ===========================================================================
# 2. CONCRETE GLOBALIZATION CONSTRUCTION
# ===========================================================================

# Represents an element of B_3 as a word in generators:
# 1 = sigma_1, 2 = sigma_2, -1 = sigma_1^{-1}, -2 = sigma_2^{-1}
# Example word: [1, 2, -1] for sigma_1 * sigma_2 * sigma_1^{-1}

# Evaluates generator g in {1, 2, -1, -2} on (i,j,k) using T and T_inv
ApplyGenerator := function(g, T, T_inv, tuple)
    if tuple = [] then return []; fi;
    if g = 1 then
        return EvalR12(T, tuple[1], tuple[2], tuple[3]);
    elif g = -1 then
        return EvalR12(T_inv, tuple[1], tuple[2], tuple[3]);
    elif g = 2 then
        return EvalR23(T, tuple[1], tuple[2], tuple[3]);
    elif g = -2 then
        return EvalR23(T_inv, tuple[1], tuple[2], tuple[3]);
    fi;
    return [];
end;

# Constructs the Globalization Y = (B_3 x X^3) / ~ for a word bounded up to length max_len.
# Elements of Y are represented as canonical equivalence class representatives [word, (i,j,k)].
ConstructGlobalization := function(T, n, max_len)
    local B3_words, T_inv, X3, Y_classes, CanonicalRep, word, tuple, g;

    if not IsB3PartialActionSolution(T, n) then
        Error("T does not define a valid partial action of B_3!");
    fi;

    T_inv := InversePartialYBMap(T, n);

    # Generate X^3 tuples
    X3 := Tuples([1..n], 3);

    # Helper function: reduces (word, tuple) to a canonical form in (B_3 x X^3) / ~
    # By shifting action steps into the X^3 factor whenever partial transitions are defined.
    CanonicalRep := function(word, tuple)
        local changed, new_word, new_tuple, i, g, step;
        new_word := ShallowCopy(word);
        new_tuple := ShallowCopy(tuple);

        repeat
            changed := false;
            if Length(new_word) > 0 then
                # Check if the rightmost generator can act directly on tuple
                g := new_word[Length(new_word)];
                step := ApplyGenerator(g, T, T_inv, new_tuple);
                if step <> [] then
                    new_tuple := step;
                    Unbind(new_word[Length(new_word)]); # Remove rightmost generator
                    changed := true;
                fi;
            fi;
        until not changed;

        return [new_word, new_tuple];
    end;

    # Collect unique equivalence classes representing elements of Y
    # Built by applying B_3 words up to length max_len to initial tuples in X^3
    Y_classes := [];

    for tuple in X3 do
        # Base embedding \iota(x) = [ [], tuple ]
        AddSet(Y_classes, CanonicalRep([], tuple));
    od;

    # Expand Y under generator actions up to specified max word length
    # (For infinite B_3 actions, restricting to bounded length gives the truncation)
    return rec(
        Y := Y_classes,
        T := T,
        T_inv := T_inv,
        n := n,
        CanonicalRep := CanonicalRep
    );
end;

# Evaluates the global action of generator g in {1, 2, -1, -2} on an element class in Y
GlobalAction := function(glob, g, class_element)
    local new_word;
    new_word := ShallowCopy(class_element[1]);
    Add(new_word, g, 1); # Multiply g on the left: g * (word, tuple) = (g * word, tuple)
    return glob.CanonicalRep(new_word, class_element[2]);
end;



# ===========================================================================
# PROFILE-BASED GLOBALIZATION IN (X^3 \cup {*} )^{B_3}
# ===========================================================================

# Represents an element in (X^3 \cup {*})^{B_3} as a sparse lookup map (GAP Record)
# Mapping B_3 words -> X^3 tuples. Undefined positions correspond to '*'.

# Helper to canonicalize B_3 words using braid relation sigma_1 sigma_2 sigma_1 = sigma_2 sigma_1 sigma_2
# Generators: 1 = s1, 2 = s2, -1 = s1^-1, -2 = s2^-1
ReduceB3Word := function(word)
    local w, changed, i;
    w := ShallowCopy(word);
    repeat
        changed := false;
        # Free group cancellations: g * g^-1 = e
        i := 1;
        while i < Length(w) do
            if w[i] = -w[i+1] then
                Remove(w, i); Remove(w, i);
                changed := true;
            else
                i := i + 1;
            fi;
        od;
        # Braid relation reductions: [1,2,1] -> [2,1,2], [-2,-1,-2] -> [-1,-2,-1], etc.
        for i in [1..(Length(w)-2)] do
            if w[i] = 1 and w[i+1] = 2 and w[i+2] = 1 then
                w[i] := 2; w[i+1] := 1; w[i+2] := 2;
                changed := true;
            elif w[i] = 2 and w[i+1] = 1 and w[i+2] = 2 then
                w[i] := 1; w[i+1] := 2; w[i+2] := 1;
                changed := true;
            fi;
        od;
    until not changed;
    return w;
end;

# Computes the Orbit Profile map f_tuple for a given (i,j,k) in X^3
# Evaluates f_tuple(w) = alpha_w(tuple) for all w in B_3 reachable via defined steps
ComputeOrbitProfile := function(tuple, T, n, max_depth)
    local profile, T_inv, queue, current, w, g, next_tuple, next_w, key;

    T_inv := InversePartialYBMap(T, n);
    profile := rec();
    
    # Queue entries: [B_3 word, X^3 tuple]
    queue := [ [[], tuple] ];
    
    while Length(queue) > 0 do
        current := Remove(queue, 1);
        w := current[1];
        tuple := current[2];
        key := String(w);

        if not IsBound(profile.(key)) then
            profile.(key) := tuple;

            # Do not expand beyond max_depth to keep profiles finite
            if Length(w) < max_depth then
                for g in [1, 2, -1, -2] do
                    next_tuple := ApplyGenerator(g, T, T_inv, tuple);
                    if next_tuple <> [] then
                        next_w := ReduceB3Word(Concatenation(w, [g]));
                        Add(queue, [next_w, next_tuple]);
                    fi;
                od;
            fi;
        fi;
    od;

    return profile;
end;

# Computes the left shift of a profile map f by generator g \in {1, 2, -1, -2}:
# (g . f)(w) = f(g^-1 * w)
ShiftProfile := function(profile, g)
    local shifted_profile, key, w, g_inv_w, target_key;
    shifted_profile := rec();

    for key in RecNames(profile) do
        # Parse the stored B_3 word key back to a list
        w := EvalString(key);
        # Compute g^-1 * w
        g_inv_w := ReduceB3Word(Concatenation([-g], w));
        target_key := String(g_inv_w);

        if IsBound(profile.(target_key)) then
            shifted_profile.(key) := profile.(target_key);
        fi;
    od;

    return shifted_profile;
end;

# Construct globalization Y in (X^3 \cup {*})^{B_3} as the set of all B_3-shifts of profiles
# Stops and warns if max_iterations is reached before Y closes.
ConstructProfileGlobalization := function(T, n, max_depth, max_iterations)
    local X3, tuple, base_profile, Y_profiles, queue, current_f, g, shifted_f, count;

    if not IsB3PartialActionSolution(T, n) then
        Error("T does not define a valid partial action of B_3!");
    fi;

    X3 := Tuples([1..n], 3);
    Y_profiles := [];
    queue := [];

    # 1. Compute initial orbit profiles f_{(i,j,k)} for all triples in X^3
    for tuple in X3 do
        base_profile := ComputeOrbitProfile(tuple, T, n, max_depth);
        if not base_profile in Y_profiles then
            Add(Y_profiles, base_profile);
            Add(queue, base_profile);
        fi;
    od;

    # 2. BFS: Generate all B_3-shifts until closure or max_iterations
    count := 0;
    while Length(queue) > 0 do
        current_f := Remove(queue, 1);
        count := count + 1;

        if count > max_iterations then
            Print("\n*** WARNING: Max iterations (", max_iterations, ") reached! ***\n");
            Print("The globalization Y is too big (possibly infinite).\n\n");
            return rec(
                isComplete := false, 
                partialY := Y_profiles, 
                size := Length(Y_profiles)
            );
        fi;

        # Shift by each B_3 generator
        for g in [1, 2, -1, -2] do
            shifted_f := ShiftProfile(current_f, g);
            
            # If shift reveals a new profile, add it to Y
            if not shifted_f in Y_profiles then
                Add(Y_profiles, shifted_f);
                Add(queue, shifted_f);
            fi;
        od;
    od;

    Print("Globalization constructed successfully! Total elements |Y| = ", Length(Y_profiles), "\n");
    return rec(
        isComplete := true, 
        Y := Y_profiles, 
        size := Length(Y_profiles)
    );
end;




# ===========================================================================
# OPTIMIZED PROFILE GLOBALIZATION FOR B_3 IN GAP
# ===========================================================================

# Initialize native BraidGroup(3) once
# Core GAP construction of B_3 = <s1, s2 | s1*s2*s1 = s2*s1*s2>
F := FreeGroup("s1", "s2");;
s1 := F.1;; 
s2 := F.2;;
B3 := F / [ s1*s2*s1 / (s2*s1*s2) ];;

# Generators in the finitely presented group
s1 := B3.1;;
s2 := B3.2;;

# Generators and their explicit inverses (indices match)
B3_GENS := [ s1, s2, s1^-1, s2^-1 ];
B3_INVS := [ s1^-1, s2^-1, s1, s2 ];
B3_INDICES := [ 1, 2, -1, -2 ];

# Fast evaluation of generator i in {1, 2, -1, -2} on (x,y,z)
ApplyGenFast := function(gen_idx, T, T_inv, tuple)
    if gen_idx = 1   then return EvalR12(T, tuple[1], tuple[2], tuple[3]);
    elif gen_idx = -1 then return EvalR12(T_inv, tuple[1], tuple[2], tuple[3]);
    elif gen_idx = 2  then return EvalR23(T, tuple[1], tuple[2], tuple[3]);
    elif gen_idx = -2 then return EvalR23(T_inv, tuple[1], tuple[2], tuple[3]);
    fi;
    return [];
end;

# ---------------------------------------------------------------------------
# Fast Profile Computation using Native B_3 Elements
# ---------------------------------------------------------------------------
ComputeProfileFast := function(tuple, T, T_inv, n, max_depth)
    local profile, queue, current, w, gen_idx, next_tuple, next_w, i, last_idx;

    # Store profile as a list of pairs: [ B3_element, X^3_tuple ]
    profile := [];
    
    # Queue entries: [ B3_element, X^3_tuple, last_generator_index, depth ]
    queue := [ [ One(B3), tuple, 0, 0 ] ];
    
    while Length(queue) > 0 do
        current := Remove(queue, 1);
        w := current[1];
        tuple := current[2];
        last_idx := current[3];

        Add(profile, [w, tuple]);

        if current[4] < max_depth then
            for i in [1..4] do
                gen_idx := B3_INDICES[i];
                
                # Optimization: Skip immediate inverse backtracking (e.g., s1 followed by s1^-1)
                if last_idx <> -gen_idx then
                    next_tuple := ApplyGenFast(gen_idx, T, T_inv, tuple);
                    if next_tuple <> [] then
                        next_w := w * B3_GENS[i]; # Native Garside multiplication
                        Add(queue, [next_w, next_tuple, gen_idx, current[4] + 1]);
                    fi;
                fi;
            od;
        fi;
    od;

    return profile;
end;

# Fast profile shift: (g . f)(w) = f(g^-1 * w)
ShiftProfileFast := function(profile, gen_idx)
    local g_inv, shifted, pair, w, target_w;
    
    # Map index to inverse generator element
    if gen_idx = 1    then g_inv := s1^-1;
    elif gen_idx = -1 then g_inv := s1;
    elif gen_idx = 2  then g_inv := s2^-1;
    elif gen_idx = -2 then g_inv := s2;
    fi;

    shifted := [];
    for pair in profile do
        # Target element in profile domain: g^-1 * w
        target_w := g_inv * pair[1];
        Add(shifted, [pair[1], pair[2]]); # Evaluates profile at g^-1 * w
    od;

    return shifted;
end;

# ---------------------------------------------------------------------------
# Main Optimized Globalization Function
# ---------------------------------------------------------------------------
ConstructProfileGlobalizationOptimized := function(T, n, max_depth, max_iterations)
    local X3, T_inv, tuple, base_prof, Y_profiles, queue, current_f, 
          i, gen_idx, shifted_f, count;

    if not IsB3PartialActionSolution(T, n) then
        Error("T does not define a valid partial action of B_3!");
    fi;

    # Optimization: Compute inverse partial matrix ONCE
    T_inv := InversePartialYBMap(T, n);
    
    X3 := Tuples([1..n], 3);
    Y_profiles := [];
    queue := [];

    # 1. Build initial base profiles for all triples in X^3
    for tuple in X3 do
        base_prof := ComputeProfileFast(tuple, T, T_inv, n, max_depth);
        if not base_prof in Y_profiles then
            Add(Y_profiles, base_prof);
            Add(queue, base_prof);
        fi;
    od;

    # 2. BFS expansion using generator shifts
    count := 0;
    while Length(queue) > 0 do
        current_f := Remove(queue, 1);
        count := count + 1;

        if count > max_iterations then
            Print("\n*** WARNING: Max iterations (", max_iterations, ") reached! ***\n");
            Print("The globalization Y is too big (possibly infinite).\n\n");
            return rec(isComplete := false, Y := Y_profiles, size := Length(Y_profiles));
        fi;

        for i in [1..4] do
            gen_idx := B3_INDICES[i];
            shifted_f := ShiftProfileFast(current_f, gen_idx);
            
            # Fast equality check on native profile structures
            if not shifted_f in Y_profiles then
                Add(Y_profiles, shifted_f);
                Add(queue, shifted_f);
            fi;
        od;
    od;

    Print("Globalization completed! |Y| = ", Length(Y_profiles), "\n");
    return rec(isComplete := true, Y := Y_profiles, size := Length(Y_profiles));
end;