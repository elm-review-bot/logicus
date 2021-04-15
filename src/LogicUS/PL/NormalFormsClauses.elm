module LogicUS.PL.NormalFormsClauses exposing
    ( fplContainsEquiv, fplRemoveAllEquiv, fplContainsImpl, fplRemoveAllImpl, fplInteriorizeAllNeg, fplInteriorizeAllDisj, fplInteriorizeAllConj, fplToNNF, fplToCNF, fplToDNF
    , ClausePL, ClausePLSet, cplIsPositive, cplIsNegative, cplEqClauses, cplSubsumes, cplIsTautology, csplRemoveEqClauses, csplRemoveTautClauses, csplRemoveSubsumedClauses, cplSymbols, csplSymbols, cplInterpretations, csplInterpretations, cplValuation, csplValuation, cplModels, csplModels, cplIsInsat, csplIsTaut, csplIsSat, cplSetIsInsat
    , cplFromCNF, fplToClauses, splToClauses
    , cplReadFromString, cplReadExtraction, cplToInputString
    , cplToString, cplToMathString, csplToString, csplToMathString
    )

{-| The module provides the tools for express formulas in their NN, CNF, DNF and Clausal Form.


# Normal Forms

@docs fplContainsEquiv, fplRemoveAllEquiv, fplContainsImpl, fplRemoveAllImpl, fplInteriorizeAllNeg, fplInteriorizeAllDisj, fplInteriorizeAllConj, fplToNNF, fplToCNF, fplToDNF


# Clauses

@docs ClausePL, ClausePLSet, cplIsPositive, cplIsNegative, cplEqClauses, cplSubsumes, cplIsTautology, csplRemoveEqClauses, csplRemoveTautClauses, csplRemoveSubsumedClauses, cplSymbols, csplSymbols, cplInterpretations, csplInterpretations, cplValuation, csplValuation, cplModels, csplModels, cplIsInsat, csplIsTaut, csplIsSat, cplSetIsInsat


# Formulas to Clauses

@docs cplFromCNF, fplToClauses, splToClauses


# Clauses Parser

@docs cplReadFromString, cplReadExtraction, cplToInputString


# Clauses Representation

@docs cplToString, cplToMathString, csplToString, csplToMathString

-}

--===========--
--  IMPORTS  --
--===========--

import LogicUS.PL.SintaxSemantics as PL_SS exposing (FormulaPL(..), Interpretation, Literal, PSymb, SetPL)
import Parser exposing ((|.), (|=), Parser, Trailing(..))
import String.Extra as SE



--===========--
--   TYPES   --
--===========--


{-| It represent a ClausePL as a list of literals.

    c1 : ClausePL
    c1 =
        [ Neg (Atom "p"), Neg (Atom "q"), Atom "r" ]

    c2 : ClausePL
    c2 =
        [ Neg (Atom "p"), Atom "r" ]

    c3 : ClausePL
    c3 =
        [ Atom "r" ]

-}
type alias ClausePL =
    List Literal


{-| It represent a List of ClausePL

    cs : ClausePLSet
    cs =
        [ c1, c2, c3 ]

-}
type alias ClausePLSet =
    List ClausePL



--===========--
-- FUNCTIONS --
--===========--
-----------------------
-- Auxiliar functions -
-----------------------
-- It concatenates two lists avoiding elements from second list that are in the first one.


uniqueConcatList : List a -> List a -> List a
uniqueConcatList xs ys =
    List.foldl
        (\x ac ->
            if List.member x ac then
                ac

            else
                ac ++ [ x ]
        )
        xs
        ys



-- It generates all possible sublists of a list of elements


powerset : List a -> List (List a)
powerset =
    List.foldr (\x acc -> acc ++ List.map ((::) x) acc) [ [] ]



-- It removes the spaces of a string


cleanSpaces : String -> String
cleanSpaces x =
    String.join "" <| String.split " " <| SE.clean x



--------------------------
-- Normal Forms Fuctions -
--------------------------


{-|

    It checks if the formula contains any equivalence as a part of it.

    f1 = Neg (Equi (Atom "p") (Impl (Atom "q") (Atom "r")))
    fplContainsEquiv f1 == True

    f2 = Disj (Neg (Conj (Atom "p") (Conj (Atom "q") (Atom "r")))) (Disj (Conj (Atom "p") (Atom "q")) (Atom "r"))
    fplContainsEquiv f2 == False

-}
fplContainsEquiv : FormulaPL -> Bool
fplContainsEquiv f =
    case f of
        Atom _ ->
            False

        Neg x ->
            fplContainsEquiv x

        Conj x y ->
            fplContainsEquiv x || fplContainsEquiv y

        Disj x y ->
            fplContainsEquiv x || fplContainsEquiv y

        Impl x y ->
            fplContainsEquiv x || fplContainsEquiv y

        Equi _ _ ->
            True

        Insat ->
            False


{-|

    It checks if the formula contains any implication as a part of the formula

    fplContainsImpl f1 == True

    fplContainsImpl f2 == False

-}
fplContainsImpl : FormulaPL -> Bool
fplContainsImpl f =
    case f of
        Atom _ ->
            False

        Neg x ->
            fplContainsImpl x

        Conj x y ->
            fplContainsImpl x || fplContainsImpl y

        Disj x y ->
            fplContainsImpl x || fplContainsImpl y

        Impl _ _ ->
            True

        Equi x y ->
            fplContainsImpl x || fplContainsImpl y

        Insat ->
            False


{-| It checks if the formula contains any conjunction as a part of the formula

    fplContainsConj f1 == False

    fplContainsConj f2 == True

-}
fplContainsConj : FormulaPL -> Bool
fplContainsConj f =
    case f of
        Atom _ ->
            False

        Neg x ->
            fplContainsConj x

        Conj _ _ ->
            True

        Disj x y ->
            fplContainsConj x || fplContainsConj y

        Impl x y ->
            fplContainsConj x || fplContainsConj y

        Equi x y ->
            fplContainsConj x || fplContainsConj y

        Insat ->
            False


{-|

    It checks if the formula contains any disjunction as a part of the formula

    fplContainsDisj f1 == False

    fplContainsDisj f2 == True

-}
fplContainsDisj : FormulaPL -> Bool
fplContainsDisj f =
    case f of
        Atom _ ->
            False

        Neg x ->
            fplContainsDisj x

        Conj x y ->
            fplContainsDisj x || fplContainsDisj y

        Disj _ _ ->
            True

        Impl x y ->
            fplContainsDisj x || fplContainsDisj y

        Equi x y ->
            fplContainsDisj x || fplContainsDisj y

        Insat ->
            False


{-|

    It eliminates all equivalences of a formula by replacing it with the conjunction of the corresponding implications.

    f3 = fplRemoveAllEquiv f1
    f3 == Neg (Conj (Impl (Atom "p") (Impl (Atom "q") (Atom "r"))) (Impl (Impl (Atom "q") (Atom "r")) (Atom "p")))

-}
fplRemoveAllEquiv : FormulaPL -> FormulaPL
fplRemoveAllEquiv f =
    case f of
        Atom x ->
            Atom x

        Neg x ->
            Neg (fplRemoveAllEquiv x)

        Conj x y ->
            Conj (fplRemoveAllEquiv x) (fplRemoveAllEquiv y)

        Disj x y ->
            Disj (fplRemoveAllEquiv x) (fplRemoveAllEquiv y)

        Impl x y ->
            Impl (fplRemoveAllEquiv x) (fplRemoveAllEquiv y)

        Equi x y ->
            Conj (Impl (fplRemoveAllEquiv x) (fplRemoveAllEquiv y)) (Impl (fplRemoveAllEquiv y) (fplRemoveAllEquiv x))

        Insat ->
            Insat


{-|

    It eliminates all implications of a formula by replacing it with the conjunction of the corresponding implications.

    f4 = fplRemoveAllImpl f3
    f4 == Neg (Conj (Disj (Neg (Atom "p")) (Disj (Neg (Atom "q")) (Atom "r"))) (Disj (Neg (Disj (Neg (Atom "q")) (Atom "r"))) (Atom "p")))

-}
fplRemoveAllImpl : FormulaPL -> FormulaPL
fplRemoveAllImpl f =
    case f of
        Atom x ->
            Atom x

        Neg x ->
            Neg (fplRemoveAllImpl x)

        Conj x y ->
            Conj (fplRemoveAllImpl x) (fplRemoveAllImpl y)

        Disj x y ->
            Disj (fplRemoveAllImpl x) (fplRemoveAllImpl y)

        Impl x y ->
            Disj (Neg (fplRemoveAllImpl x)) (fplRemoveAllImpl y)

        Equi x y ->
            Equi (fplRemoveAllImpl x) (fplRemoveAllImpl y)

        Insat ->
            Insat


{-|

    It interiorizes the negations by applying De Morgan's laws where appropriate

    f5 = fplInteriorizeAllNeg f2
    f5 == Disj (Disj (Neg (Atom "p")) (Disj (Neg (Atom "q")) (Neg (Atom "r")))) (Disj (Conj (Atom "p") (Atom "q")) (Atom "r"))

    f6 = fplInteriorizeAllNeg f4
    f6 == Disj (Conj (Atom "p") (Conj (Atom "q") (Neg (Atom "r")))) (Conj (Disj (Neg (Atom "q")) (Atom "r")) (Neg (Atom "p")))

-}
fplInteriorizeAllNeg : FormulaPL -> FormulaPL
fplInteriorizeAllNeg f =
    let
        fplInteriorizeAllNegAux p =
            case p of
                Atom x ->
                    Neg (Atom x)

                Neg x ->
                    fplInteriorizeAllNeg x

                Conj x y ->
                    Disj (fplInteriorizeAllNegAux x) (fplInteriorizeAllNegAux y)

                Disj x y ->
                    Conj (fplInteriorizeAllNegAux x) (fplInteriorizeAllNegAux y)

                Impl x y ->
                    Conj (fplInteriorizeAllNeg x) (fplInteriorizeAllNegAux y)

                Equi x y ->
                    Disj (fplInteriorizeAllNegAux (Impl x y)) (fplInteriorizeAllNegAux (Impl y x))

                Insat ->
                    Insat
    in
    case f of
        Atom x ->
            Atom x

        Neg x ->
            fplInteriorizeAllNegAux x

        Conj x y ->
            Conj (fplInteriorizeAllNeg x) (fplInteriorizeAllNeg y)

        Disj x y ->
            Disj (fplInteriorizeAllNeg x) (fplInteriorizeAllNeg y)

        Impl x y ->
            Impl (fplInteriorizeAllNeg x) (fplInteriorizeAllNeg y)

        Equi x y ->
            Equi (fplInteriorizeAllNeg x) (fplInteriorizeAllNeg y)

        Insat ->
            Insat


{-|

    It interiorizes the disjunctions by applying the AND Distributive law where appropriate.

    f7 = fplInteriorizeAllDisj f6
    f7 == Conj (Conj (Disj (Atom "p") (Disj (Neg (Atom "q")) (Atom "r"))) (Disj (Atom "p") (Neg (Atom "p")))) (Conj (Conj (Disj (Atom "q") (Disj (Neg (Atom "q")) (Atom "r"))) (Disj (Atom "q") (Neg (Atom "p")))) (Conj (Disj (Neg (Atom "r")) (Disj (Neg (Atom "q")) (Atom "r"))) (Disj (Neg (Atom "r")) (Neg (Atom "p")))))

-}
fplInteriorizeAllDisj : FormulaPL -> FormulaPL
fplInteriorizeAllDisj f =
    case f of
        Disj (Conj f1 f2) g ->
            fplInteriorizeAllDisj <| Conj (Disj f1 g) (Disj f2 g)

        Disj g (Conj f1 f2) ->
            fplInteriorizeAllDisj <| Conj (Disj g f1) (Disj g f2)

        Conj f1 f2 ->
            Conj (fplInteriorizeAllDisj f1) (fplInteriorizeAllDisj f2)

        Disj f1 f2 ->
            if fplContainsConj f1 then
                if fplContainsConj f2 then
                    fplInteriorizeAllDisj <| Disj (fplInteriorizeAllDisj f1) (fplInteriorizeAllDisj f2)

                else
                    fplInteriorizeAllDisj <| Disj (fplInteriorizeAllDisj f1) f2

            else if fplContainsConj f2 then
                fplInteriorizeAllDisj <| Disj f1 (fplInteriorizeAllDisj f2)

            else
                f

        _ ->
            f


{-|

    It interiorizes the disjunctions by applying the OR Distributive law where appropriate.

    f8 = fplInteriorizeAllConj f6
    f8 == Disj (Conj (Atom "p") (Conj (Atom "q") (Neg (Atom "r")))) (Disj (Conj (Neg (Atom "q")) (Neg (Atom "p"))) (Conj (Atom "r") (Neg (Atom "p"))))

-}
fplInteriorizeAllConj : FormulaPL -> FormulaPL
fplInteriorizeAllConj f =
    case f of
        Conj (Disj f1 f2) g ->
            fplInteriorizeAllConj <| Disj (Conj f1 g) (Conj f2 g)

        Conj g (Disj f1 f2) ->
            fplInteriorizeAllConj <| Disj (Conj g f1) (Conj g f2)

        Disj f1 f2 ->
            Disj (fplInteriorizeAllConj f1) (fplInteriorizeAllConj f2)

        Conj f1 f2 ->
            if fplContainsDisj f1 then
                if fplContainsDisj f2 then
                    fplInteriorizeAllConj <| Conj (fplInteriorizeAllConj f1) (fplInteriorizeAllConj f2)

                else
                    fplInteriorizeAllConj <| Disj (fplInteriorizeAllConj f1) f2

            else if fplContainsDisj f2 then
                fplInteriorizeAllConj <| Conj f1 (fplInteriorizeAllConj f2)

            else
                f

        _ ->
            f


{-|

    Express a formula in its Negation Normal Form (NNF) that is formed only by literals and the conectives ∧ and/or ∨.

    -- Check if f5 is in NNF
    (f5 == fplToNNF f5) == True

    -- Check if f1 is in NNF
    (f1 == fplToNNF f1) == False

    -- Calculate NNF form for f1
    f9 = fplToNNF f1
    f9 == Disj (Conj (Atom "p") (Conj (Atom "q") (Neg (Atom "r")))) (Conj (Disj (Neg (Atom "q")) (Atom "r")) (Neg (Atom "p")))

    -- It is equal to f6
    (f9 == f6) == True

-}
fplToNNF : FormulaPL -> FormulaPL
fplToNNF f =
    fplInteriorizeAllNeg <| fplRemoveAllImpl <| fplRemoveAllEquiv f


{-|

    Express a formula in its Conjuction Normal Form (CNF) that is formed as a conjuction of disjuntive formulas.

     -- Check if f1 is in CNF
    (f1 == fplToCNF f1) == False

    -- Check if f7 is in CNF
    (f7 == fplToCNF f7) == True

    -- Calculate CNF for f1
    f10 = fplToCNF f1
    f10 == Conj (Conj (Disj (Atom "p") (Disj (Neg (Atom "q")) (Atom "r"))) (Disj (Atom "p") (Neg (Atom "p")))) (Conj (Conj (Disj (Atom "q") (Disj (Neg (Atom "q")) (Atom "r"))) (Disj (Atom "q") (Neg (Atom "p")))) (Conj (Disj (Neg (Atom "r")) (Disj (Neg (Atom "q")) (Atom "r"))) (Disj (Neg (Atom "r")) (Neg (Atom "p")))))

    -- It is equal to f7
    (f10 == f7) == True

-}
fplToCNF : FormulaPL -> FormulaPL
fplToCNF f =
    fplInteriorizeAllDisj <| fplToNNF f


{-|

    Express a formula in its Disjunction Normal Form (CNF) that is formed as a conjuction of disjuntive formulas.

    -- Check if f1 is in DNF
    (f1 == fplToDNF f1) == False

    -- Check if f8 is in DNF
    (f8 == fplToCNF f8) == True

    -- Calculate CNF for f1
    f11 = fplToDNF f1
    f11 == Disj (Conj (Atom "p") (Conj (Atom "q") (Neg (Atom "r")))) (Disj (Conj (Neg (Atom "q")) (Neg (Atom "p"))) (Conj (Atom "r") (Neg (Atom "p"))))

    -- It is equal to f8
    (f11 == f8) == True

-}
fplToDNF : FormulaPL -> FormulaPL
fplToDNF f =
    fplInteriorizeAllConj <| fplToNNF f



--- CLAUSES


{-| It checks if the clauses are equal, that is, if both have the same elements

    (c1 == List.reverse c1) == False

    cplEqClauses c1 (List.reverse c1) == True

-}
cplEqClauses : ClausePL -> ClausePL -> Bool
cplEqClauses c1 c2 =
    List.all (\x -> List.member x c1) c2 && (List.length c1 == List.length c2)


{-| Indicates if the first clause subsumes the second, that is, if the first is entirely contained in the second.

    cplSubsumes c1 c2 == False

    cplSubsumes c2 c1 == True

-}
cplSubsumes : ClausePL -> ClausePL -> Bool
cplSubsumes c1 c2 =
    List.all (\x -> List.member x c2) c1


{-| Indicates if the clause is a tautology, that is if it contains a literal and its complement.

    cplIsTautology c1 == False

    (cplIsTautology <| c1 ++ [ Atom "p" ]) == True

-}
cplIsTautology : ClausePL -> Bool
cplIsTautology c =
    List.any (\x -> List.member (PL_SS.fplNegation x) c) c


{-| Indicates if the clause is enterly positive, this is with all its literals positive

    cplIsPositive c1 == False

    cplIsPositive c3 == True

-}
cplIsPositive : ClausePL -> Bool
cplIsPositive c =
    List.all PL_SS.fplIsPositiveLiteral c


{-| Indicates if the clause is enterly negative, this is with all its literals negative

    cplIsNegative c1 == False

    cplIsNegative (List.take 2 c1) == True

-}
cplIsNegative : ClausePL -> Bool
cplIsNegative c =
    List.all PL_SS.fplIsNegativeLiteral c


{-| It removes clauses that are equal from a list of clauses

    cs1 = [c1, c2, c3]

    csplRemoveEqClauses c1 == c1

    csplRemoveEqClauses (cs1 ++ (List.map (List.reverse) cs1)) == c1

-}
csplRemoveEqClauses : ClausePLSet -> ClausePLSet
csplRemoveEqClauses xs =
    List.foldl
        (\x ac ->
            if List.any (\y -> cplEqClauses y x) ac then
                ac

            else
                ac ++ [ x ]
        )
        []
        xs


{-| It removes clauses that are tautological clauses

    csplRemoveTautClauses <| List.map (\x -> x ++ [ Atom "q" ]) cs1 == [ [ Neg (Atom "p"), Atom "r", Atom "q" ], [ Atom "r", Atom "q" ] ]

-}
csplRemoveTautClauses : ClausePLSet -> ClausePLSet
csplRemoveTautClauses cs =
    List.filter (not << cplIsTautology) cs


{-| It removes clauses that are subsumed by other from the list

    csplRemoveSubsumedClauses cs1 == [ [ Atom "r" ] ]

-}
csplRemoveSubsumedClauses : ClausePLSet -> ClausePLSet
csplRemoveSubsumedClauses cs =
    List.foldl
        (\c ac ->
            if List.any (\x -> cplSubsumes x c) ac then
                ac

            else
                List.filter (not << cplSubsumes c) ac ++ [ c ]
        )
        []
        cs


{-| It gives the propositional symbols that take place in the clause

    cplSymbols c1 =
        [ "p", "q", "r" ]
    cplSymbols c2 =
        [ "p", "r" ]
    cplSymbols c3 =
        [ "r" ]

-}
cplSymbols : ClausePL -> List PSymb
cplSymbols c =
    List.sort <| PL_SS.splSymbols c


{-| It gives the propositional symbols that take place in the clause

    csplSymbols cs1 =
        [ "p", "q", "r" ]

-}
csplSymbols : ClausePLSet -> List PSymb
csplSymbols cs =
    List.sort <| List.foldl (\c ac -> uniqueConcatList ac (cplSymbols c)) [] cs


{-| It gives all possible interpretations for a clause

    cplInterpretations c1 == [ [], [ "p" ], [ "p", "q" ], [ "p", "q", "r" ], [ "p", "r" ], [ "q" ], [ "q", "r" ], [ "r" ] ]

    cplInterpretation c2 == [ [], [ "p" ], [ "p", "r" ], [ "r" ] ]

-}
cplInterpretations : ClausePL -> List Interpretation
cplInterpretations c =
    List.sort <| powerset <| cplSymbols c


{-| It gives all possible interpretations for a set of clauses

    csplInterpretations cs1 == [ [], [ "p" ], [ "p", "q" ], [ "p", "q", "r" ], [ "p", "r" ], [ "q" ], [ "q", "r" ], [ "r" ] ]

    csplInterpretations [ [ Atom "p" ], [ Atom "q" ] ] == [ [], [ "p" ], [ "p", "q" ], [ "q" ] ]

-}
csplInterpretations : ClausePLSet -> List Interpretation
csplInterpretations cs =
    List.sort <| powerset <| csplSymbols cs


{-| It evaluates the truth value of the clause regarding to a interpretation

    cplValuation c2 [ "p", "r" ] == True

    cplValuation c2 [] == True

    cplValuation c2 [ "p" ] == False

-}
cplValuation : ClausePL -> Interpretation -> Bool
cplValuation c i =
    List.any
        (\l ->
            case l of
                Atom x ->
                    List.member x i

                Neg (Atom x) ->
                    not <| List.member x i

                _ ->
                    False
        )
        c


{-| It evaluates the truth value of a set of clauses regarding to a interpretation

    csplValuation cs1 [ "r" ] == True

    csplValuation cs1 [] == False

-}
csplValuation : ClausePLSet -> Interpretation -> Bool
csplValuation cs i =
    List.all (\c -> cplValuation c i) cs


{-| It generates all models of a clause by bruteforce, valuating the truth value for each interpretation

    plModels c1 == [ [], [ "p" ], [ "p", "q", "r" ], [ "p", "r" ], [ "q" ], [ "q", "r" ], [ "r" ] ]

    cplModels c2 == [ [], [ "p", "r" ], [ "r" ] ]

    cplModels c3 == [ [ "r" ] ]

-}
cplModels : ClausePL -> List Interpretation
cplModels c =
    List.filter (\i -> cplValuation c i) <| cplInterpretations c


{-| It generates all models of a set of clauses by bruteforce, valuating the truth value for each interpretation

    csplModels cs1 == [ [ "p", "q", "r" ], [ "p", "r" ], [ "q", "r" ], [ "r" ] ]

-}
csplModels : ClausePLSet -> List Interpretation
csplModels cs =
    List.filter (\i -> csplValuation cs i) <| csplInterpretations cs


{-| It checks if a clause is unsatisfible, that is if it is empty.

    cplIsInsat c1 == False

    cplIsInsat c2 == False

    cplIsInsat [] == True

-}
cplIsInsat : ClausePL -> Bool
cplIsInsat c =
    List.isEmpty c


{-| It checks if a set of clauses is a tautology, that is if all clauses are tautologies.

    csplIsTaut cs1 == False

    csplIsTaut (List.map (\x -> x ++ [ Neg (Atom "r") ]) cs1) == True

-}
csplIsTaut : ClausePLSet -> Bool
csplIsTaut cs =
    List.all (\c -> cplIsTautology c) cs


{-| It checks if a set of clauses is satisfiable by bruteforce, calculating its models and checking any exists

    csplIsSat cs1 == True

    csplIsSat (cs1 ++ [ Neg (Atom "r") ]) == False

-}
csplIsSat : ClausePLSet -> Bool
csplIsSat cs =
    not <| List.isEmpty <| csplModels cs


{-| It checks if a set of clauses are satisfiable by brute force, calculates its models and verifies that none exist.
-}
cplSetIsInsat : ClausePLSet -> Bool
cplSetIsInsat cs =
    List.isEmpty <| csplModels cs



-- From formulas to clauses


{-| Express a CNF formula as a Set of clauses. If input is not in CNF form Nothing is returned

    fplToCNF f1 |> cplFromCNF == Just [ [ Atom "p" ], [ Neg (Atom "q") ], [ Atom "r" ], [ Neg (Atom "p") ], [ Atom "q" ], [ Neg (Atom "r") ] ]

    fplToDNF f1 |> cplFromCNF == Nothing

-}
cplFromCNF : FormulaPL -> Maybe ClausePLSet
cplFromCNF f =
    if f == fplToCNF f then
        Just <| cplFromCNFAux f

    else
        Nothing



-- It pass a CNF formula to a Set of clausses


cplFromCNFAux : FormulaPL -> ClausePLSet
cplFromCNFAux f =
    csplRemoveEqClauses <|
        case f of
            Conj f1 f2 ->
                uniqueConcatList (cplFromCNFAux f1) (cplFromCNFAux f2)

            Atom _ ->
                [ [ f ] ]

            Neg (Atom _) ->
                [ [ f ] ]

            Disj x1 x2 ->
                [ uniqueConcatList (List.concat <| cplFromCNFAux x1) (List.concat <| cplFromCNFAux x2) ]

            _ ->
                []


{-| Express a formula as a Set of clauses.
fplToClauses f1 == [[Atom "p"],[Neg (Atom "q")],[Atom "r"],[Neg (Atom "p")],[Atom "q"],[Neg (Atom "r")]]
-}
fplToClauses : FormulaPL -> ClausePLSet
fplToClauses f =
    cplFromCNFAux <| fplToCNF f


{-| Express a set of formulas as a Set of clauses.

    fs = List.map (fplReadExtraction << fplReadFromString) ["p->q", "p \\/ q -> r", "¬p \\/ q"]
    cs = splToClauses fs
    cs == [[Neg (Atom "p"),Atom "q"],[Neg (Atom "p"),Atom "r"],[Neg (Atom "q"),Atom "r"]]

-}
splToClauses : SetPL -> ClausePLSet
splToClauses fs =
    csplRemoveEqClauses <| List.concat <| List.map fplToClauses fs



--===========--
--  PARSER   --
--===========--


{-| It reads the formula from a string. It returns a tuple with may be a formula (if it can be read it) and a message of error it it cannot.

    cplReadFromString "p_{1}, p_{2}, ¬q_{1}, q_{2}" == ( Just [ Atom "p_{1}", Atom "p_{2}", Neg (Atom "q_{1}"), Atom "q_{2}" ], "", "" )

    cplReadFromString "{p_{1}, p_{2}, ¬q_{1}, q_{2}}" == ( Just [ Atom "p_{1}", Atom "p_{2}", Neg (Atom "q_{1}"), Atom "q_{2}" ], "", "" )

    cplReadFromString "{p_{1}, p_{2}, ¬q_{1}, q_{2}" == ( Nothing, "{p_{1}, p_{2}, ¬q_{1}, q_{2}", "Error: [{ col = 29, problem = Expecting ',', row = 1 },{ col = 29, problem = Expecting '}', row = 1 }]" )

    cplReadFromString "{p_{1}, p_{2}, ¬q_{1}, q_{2}" == ( Nothing, "{p_{1}, p_{2}, ¬q_{1}, q_{2}", "Error: [{ col = 29, problem = Expecting ',', row = 1 },{ col = 29, problem = Expecting '}', row = 1 }]" )

    cplReadFromString "{}" == ( Just [], "", "" )

    cplReadFromString "" == ( Nothing, "", "Argument is empty" )

-}
cplReadFromString : String -> ( Maybe ClausePL, String, String )
cplReadFromString x =
    let
        clean_x =
            cleanSpaces x
    in
    case String.left 1 <| clean_x of
        "" ->
            ( Maybe.Nothing, "", "Argument is empty" )

        "{" ->
            case Parser.run cplParser clean_x of
                Ok y ->
                    ( Maybe.Just y, "", "" )

                Err y ->
                    ( Maybe.Nothing, clean_x, "Error: " ++ String.replace "\"" "'" (Debug.toString y) )

        _ ->
            case Parser.run cplParser ("{" ++ clean_x ++ "}") of
                Ok y ->
                    ( Maybe.Just y, "", "" )

                Err y ->
                    ( Maybe.Nothing, "{" ++ clean_x ++ "}", "Error: " ++ String.replace "\"" "'" (Debug.toString y) )


{-| It extracts the clause readed. If it is Nothing then it returns an empty clause

    (cplReadExtraction << cplReadFromString) "p_{1}, p_{2}, ¬q_{1}, q_{2}" == [ Atom "p_{1}", Atom "p_{2}", Neg (Atom "q_{1}"), Atom "q_{2}" ]

    (cplReadExtraction << cplReadFromString) "{p_{1}, p_{2}, ¬q_{1}, q_{2}" == []

    (cplReadExtraction << cplReadFromString) "{}" == []

-}
cplReadExtraction : ( Maybe ClausePL, String, String ) -> ClausePL
cplReadExtraction ( c, _, _ ) =
    Maybe.withDefault [] c


{-| It gives the corresponding input syntax of a clause

    cplToInputString c1 == "¬p,¬q,r"

    cplToInputString c3 == "r"

-}
cplToInputString : ClausePL -> String
cplToInputString c =
    case c of
        [] ->
            "{}"

        _ ->
            String.join "," <| List.map PL_SS.fplToInputString c



--- Parser Builder Functions
-- It defines the syntax of a propositional variable that can be subscripting or not


plVarParser : Parser PSymb
plVarParser =
    Parser.oneOf
        [ Parser.succeed ()
            |. Parser.backtrackable plVarSubindexedParser
        , Parser.succeed ()
            |. Parser.chompIf Char.isLower
            |. Parser.chompWhile Char.isLower
        ]
        |> Parser.getChompedString


plVarSubindexedParser : Parser PSymb
plVarSubindexedParser =
    Parser.succeed ()
        |. Parser.chompIf Char.isLower
        |. Parser.chompWhile Char.isLower
        |. Parser.sequence
            { start = "_{"
            , separator = ","
            , end = "}"
            , spaces = Parser.spaces
            , item = Parser.int
            , trailing = Forbidden
            }
        |> Parser.getChompedString


cplParser : Parser ClausePL
cplParser =
    Parser.succeed identity
        |= cplParserAux
        |. Parser.end


cplParserAux : Parser ClausePL
cplParserAux =
    Parser.sequence
        { start = "{"
        , separator = ","
        , end = "}"
        , spaces = Parser.spaces
        , item = literalParser
        , trailing = Optional
        }


literalParser : Parser Literal
literalParser =
    Parser.oneOf
        [ Parser.succeed (PL_SS.fplNegation << Atom)
            |. Parser.symbol "¬"
            |= plVarParser
        , Parser.succeed Atom
            |= plVarParser
        ]



--================--
-- REPRESENTATION --
--================--


{-| It generates the String representation of a ClausePL using unicode symbols.

    cplToString c1 == "{¬ p, ¬ q, r}"

-}
cplToString : ClausePL -> String
cplToString c =
    if List.isEmpty c then
        "□"

    else
        PL_SS.splToString c


{-| It generates the Latex string of a ClausePL. The result requires a math enviroment to be displayed.

    cplToMathString c1 == "\\left\\lbrace \\neg p, \\neg q, r\\right\\rbrace"

-}
cplToMathString : ClausePL -> String
cplToMathString c =
    if List.isEmpty c then
        "\\Box"

    else
        PL_SS.splToMathString c


{-| It generates the String representation of a Set of Clauses using unicode symbols.

    csplToString cs == "{{¬ p, q},{¬ p, r},{¬ q, r}}"

-}
csplToString : ClausePLSet -> String
csplToString cs =
    "{" ++ (String.join "," <| List.map cplToString cs) ++ "}"


{-| It generates the Latex string of a Set of Clauses. The result requires a math enviroment to be displayed.

    csplToMathString cs == "\\left\\lbrace\\left\\lbrace \\neg p, q\\right\\rbrace, \\, \\left\\lbrace \\neg p, r\\right\\rbrace, \\, \\left\\lbrace \\neg q, r\\right\\rbrace\\right\\rbrace"

-}
csplToMathString : ClausePLSet -> String
csplToMathString cs =
    "\\left\\lbrace" ++ (String.join ", \\, " <| List.map (\x -> cplToMathString x) cs) ++ "\\right\\rbrace"
