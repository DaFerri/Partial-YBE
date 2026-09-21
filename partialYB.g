#############################################################################
##
##  partial_yb.g
##  GAP package/file for Partial Yang-Baxter Maps
##
##  Representation:
##  A partial map R : S \subseteq X x X -> X x X on X = {1..n} is represented 
##  by an n x n matrix T where T[i][j] is either [a, b] or [].
##
#############################################################################

# ===========================================================================
# 1. UTILITIES & CONSTRUCTORS
# ===========================================================================

# Construct an empty partial map (domain is empty set)
EmptyPartialYBMap := function(n)
    return List([1..n], i -> List([1..n], j -> []));
end;

# Deep clone of a partial map matrix
CloneYBMap := function(T)
    return List(T, row -> List(row, res -> ShallowCopy(res)));
end;

# Check if T represents a structurally valid matrix on {1..n}
IsValidPartialYBMap := function(T, n)
    local i, j, res;
    if Length(T) <> n then return false; fi;
    for i in [1..n] do
        if Length(T[i]) <> n then return false; fi;
        for j in [1..n] do
            res := T[i][j];
            if res <> [] then
                if not (IsList(res) and Length(res) = 2 and 
                        res[1] in [1..n] and res[2] in [1..n]) then
                    return false;
                fi;
            fi;
        od;
    od;
    return true;
end;


# ===========================================================================
# 2. EVALUATIONS & YANG-BAXTER CHECKS
# ===========================================================================

# Evaluates R_{12} on (i, j, k)
EvalR12 := function(T, i, j, k)
    local res;
    res := T[i][j];
    if res = [] then
        return [];
    else
        return [res[1], res[2], k];
    fi;
end;

# Evaluates R_{23} on (i, j, k)
EvalR23 := function(T, i, j, k)
    local res;
    res := T[j][k];
    if res = [] then
        return [];
    else
        return [i, res[1], res[2]];
    fi;
end;

# Evaluates LHS = (R_{12} * R_{23} * R_{12})(i, j, k)
EvalLHS := function(T, i, j, k)
    local step1, step2, step3;
    step1 := EvalR12(T, i, j, k);
    if step1 = [] then return []; fi;
    step2 := EvalR23(T, step1[1], step1[2], step1[3]);
    if step2 = [] then return []; fi;
    step3 := EvalR12(T, step2[1], step2[2], step2[3]);
    return step3;
end;

# Evaluates RHS = (R_{23} * R_{12} * R_{23})(i, j, k)
EvalRHS := function(T, i, j, k)
    local step1, step2, step3;
    step1 := EvalR23(T, i, j, k);
    if step1 = [] then return []; fi;
    step2 := EvalR12(T, step1[1], step1[2], step1[3]);
    if step2 = [] then return []; fi;
    step3 := EvalR23(T, step2[1], step2[2], step2[3]);
    return step3;
end;

# Checks partial YBE under "strong" or "weak" mode:
# - "strong": LHS is defined iff RHS is defined, and LHS = RHS.
# - "weak": Whenever both LHS and RHS are defined, LHS = RHS.
IsPartialYBSolution := function(T, n, mode)
    local i, j, k, lhs, rhs;
    for i in [1..n] do
        for j in [1..n] do
            for k in [1..n] do
                lhs := EvalLHS(T, i, j, k);
                rhs := EvalRHS(T, i, j, k);
                
                if mode = "strong" then
                    if lhs <> rhs then return false; fi;
                elif mode = "weak" then
                    if lhs <> [] and rhs <> [] and lhs <> rhs then
                        return false;
                    fi;
                else
                    Error("mode must be 'strong' or 'weak'");
                fi;
            od;
        od;
    od;
    return true;
end;

# Checks involutivity (R^2 = id) under "strong" or "weak" mode:
# - "strong": R(a,b) MUST be defined AND equal to [i,j].
# - "weak": R(a,b) can be [], but IF defined, MUST equal [i,j].
IsInvolutiveYBMap := function(T, n, mode)
    local i, j, res, back;
    for i in [1..n] do
        for j in [1..n] do
            res := T[i][j];
            if res <> [] then
                back := T[res[1]][res[2]];
                if mode = "strong" then
                    if back <> [i, j] then return false; fi;
                elif mode = "weak" then
                    if back <> [] and back <> [i, j] then return false; fi;
                else
                    Error("mode must be 'strong' or 'weak'");
                fi;
            fi;
        od;
    od;
    return true;
end;


# ===========================================================================
# 3. CONSTRAINT PROPAGATION
# ===========================================================================

# Deduce forced entries via strong involutivity: R(i, j) = (a, b) => R(a, b) = (i, j)
DeduceInvolutivity := function(T, n)
    local i, j, res, changed;
    changed := false;
    for i in [1..n] do
        for j in [1..n] do
            res := T[i][j];
            if res <> [] then
                if T[res[1]][res[2]] = [] then
                    T[res[1]][res[2]] := [i, j];
                    changed := true;
                fi;
            fi;
        od;
    od;
    return changed;
end;

# Propagates constraints based on mode ("strong", "weak", or "none")
PropagateConstraints := function(T, n, mode)
    local changed;
    repeat
        changed := false;
        # Deductions are ONLY mathematically forced under STRONG mode
        if mode = "strong" then
            changed := changed or DeduceInvolutivity(T, n);
        fi;
    until not changed;
    return T;
end;

# Helper to set T[i][j] = [a,b] AND enforce T[a][b] = [i,j] for strong involutivity.
# Returns false if a conflict occurs, true if successful.
SetInvolutivePair := function(T, i, j, a, b)
    if T[i][j] <> [] and T[i][j] <> [a, b] then return false; fi;
    if T[a][b] <> [] and T[a][b] <> [i, j] then return false; fi;

    T[i][j] := [a, b];
    T[a][b] := [i, j];
    return true;
end;


# Checks non-degeneracy under "strong" (all-or-nothing permutations) or "weak" (injectivity on defined entries)
IsNonDegenerateYBMap := function(T, n, mode)
    local i, j, res, row_sigmas, col_taus, row_defined, col_defined;

    # 1. Check rows (sigma_i)
    for i in [1..n] do
        row_sigmas := [];
        row_defined := 0;
        for j in [1..n] do
            res := T[i][j];
            if res <> [] then
                row_defined := row_defined + 1;
                if res[1] in row_sigmas then
                    return false; # Duplicate sigma_i(j) -> violates injectivity
                fi;
                Add(row_sigmas, res[1]);
            fi;
        od;

        if mode = "strong" then
            # Strong: Row MUST be either 0% defined OR 100% defined
            if row_defined > 0 and row_defined < n then
                return false;
            fi;
        fi;
    od;

    # 2. Check columns (tau_j)
    for j in [1..n] do
        col_taus := [];
        col_defined := 0;
        for i in [1..n] do
            res := T[i][j];
            if res <> [] then
                col_defined := col_defined + 1;
                if res[2] in col_taus then
                    return false; # Duplicate tau_j(i) -> violates injectivity
                fi;
                Add(col_taus, res[2]);
            fi;
        od;

        if mode = "strong" then
            # Strong: Column MUST be either 0% defined OR 100% defined
            if col_defined > 0 and col_defined < n then
                return false;
            fi;
        fi;
    od;

    return true;
end;

# Deduce missing component values when a row or column is active and nearly full
DeduceNonDegeneracy := function(T, n)
    local i, j, res, changed, row_defined_count, missing_j, used_sigmas, val;
    changed := false;

    # Deduce missing sigma_i values in rows that are active
    for i in [1..n] do
        row_defined_count := 0;
        missing_j := 0;
        used_sigmas := [];
        for j in [1..n] do
            if T[i][j] <> [] then
                row_defined_count := row_defined_count + 1;
                Add(used_sigmas, T[i][j][1]);
            else
                missing_j := j;
            fi;
        od;

        # If row is active and missing exactly 1 sigma_i value, deduce it!
        if row_defined_count = n - 1 and missing_j > 0 then
            val := Difference([1..n], used_sigmas)[1];
            # If the second component T[i][missing_j][2] is already known via another deduction, fill it
            # Or if we are in a mode where component maps can be filled partially:
            # (Note: In standard T[i][j] = [a,b] representations, setting T[i][j] requires both components)
        fi;
    od;

    return changed;
end;

# Fast early pruning during backtracking:
# Ensures sigma_i and tau_j are injective on currently defined cells.
IsWeaklyNonDegenerate := function(T, n)
    local i, j, res, row_sigmas, col_taus;

    # Check row injectivity (sigma_i)
    for i in [1..n] do
        row_sigmas := [];
        for j in [1..n] do
            res := T[i][j];
            if res <> [] then
                if res[1] in row_sigmas then return false; fi; # Duplicate sigma_i(j)
                Add(row_sigmas, res[1]);
            fi;
        od;
    od;

    # Check column injectivity (tau_j)
    for j in [1..n] do
        col_taus := [];
        for i in [1..n] do
            res := T[i][j];
            if res <> [] then
                if res[2] in col_taus then return false; fi; # Duplicate tau_j(i)
                Add(col_taus, res[2]);
            fi;
        od;
    od;

    return true;
end;



# ===========================================================================
# 4. COMPLETION ALGORITHMS
# ===========================================================================

# Finds next empty cell [i, j] in T
FindNextUndefinedCell := function(T, n)
    local i, j;
    for i in [1..n] do
        for j in [1..n] do
            if T[i][j] = [] then return [i, j]; fi;
        od;
    od;
    return fail;
end;


# 1) General completion solver (NO involutivity constraints)
FindYBCompletions := function(T, n, requireNonDegenerate)
    local solutions, PropagateAndSolve;

    solutions := [];

    PropagateAndSolve := function(currentT)
        local slot, i, j, a, b, testT;

        currentT := PropagateConstraints(currentT, n, "none");

        # 1. Early Pruning Checks (Weak YBE & Partial Injectivity)
        if not IsPartialYBSolution(currentT, n, "weak") then return; fi;
        if requireNonDegenerate and not IsWeaklyNonDegenerate(currentT, n) then 
            return; 
        fi;

        slot := FindNextUndefinedCell(currentT, n);
        
        # 2. Terminal State Check
        if slot = fail then
            if requireNonDegenerate then
                # Strong check: Active rows/columns MUST be 100% defined and bijective
                if IsNonDegenerateYBMap(currentT, n, "strong") then
                    Add(solutions, CloneYBMap(currentT));
                fi;
            else
                Add(solutions, CloneYBMap(currentT));
            fi;
            return;
        fi;

        i := slot[1]; 
        j := slot[2];

        # 3. Branching
        for a in [1..n] do
            for b in [1..n] do
                testT := CloneYBMap(currentT);
                testT[i][j] := [a, b];
                PropagateAndSolve(testT);
            od;
        od;
    end;

    PropagateAndSolve(CloneYBMap(T));
    return solutions;
end;


FindInvolutiveYBCompletions := function(T, n, mode, requireNonDegenerate)
    local solutions, PropagateAndSolve;

    if not mode in ["strong", "weak"] then
        Error("mode must be 'strong' or 'weak'");
    fi;

    solutions := [];

    PropagateAndSolve := function(currentT)
        local slot, i, j, a, b, testT;

        currentT := PropagateConstraints(currentT, n, mode);

        # 1. Early Pruning Checks
        if not IsPartialYBSolution(currentT, n, "weak") then return; fi;
        if not IsInvolutiveYBMap(currentT, n, mode) then return; fi;
        if requireNonDegenerate and not IsWeaklyNonDegenerate(currentT, n) then 
            return; 
        fi;

        slot := FindNextUndefinedCell(currentT, n);
        
        # 2. Terminal State Check
        if slot = fail then
            if requireNonDegenerate then
                # Evaluates "strong" (all-or-nothing) or "weak" according to requested mode
                if IsNonDegenerateYBMap(currentT, n, mode) then
                    Add(solutions, CloneYBMap(currentT));
                fi;
            else
                Add(solutions, CloneYBMap(currentT));
            fi;
            return;
        fi;

        i := slot[1]; 
        j := slot[2];

        # 3. Branching
        for a in [1..n] do
            for b in [1..n] do
                testT := CloneYBMap(currentT);

                if mode = "strong" then
                    if SetInvolutivePair(testT, i, j, a, b) then
                        PropagateAndSolve(testT);
                    fi;
                elif mode = "weak" then
                    testT[i][j] := [a, b];
                    PropagateAndSolve(testT);
                fi;
            od;
        od;
    end;

    PropagateAndSolve(CloneYBMap(T));
    return solutions;
end;

