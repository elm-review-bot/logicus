module LogicUS.PL.Resolution exposing
    ( ResolutionTableau
    , cplResolventByPSymb, cplAllResolvents, csplAllResolventsByPsymb, csplResolventsByClause, csplAllResolvents
    , csplSaturationResolution, csplRegularResolution
    , csplSCFResolution, csplSCFLinearResolution, csplSCFPositiveResolution, csplSCFNegativeResolution
    , csplSCFUnitaryResolution, csplSCFByEntriesResolution
    , resolutionTableauToString, resolutionTableauToDOT
    )

{-| The module provides the tools for aplying the differents resolution strategies to a set of propositional clauses for verifying its unfeasibility.


# Types

@docs ResolutionTableau


# Resolvents

@docs cplResolventByPSymb, cplAllResolvents, csplAllResolventsByPsymb, csplResolventsByClause, csplAllResolvents


# Saturation and Regular Resolution

@docs csplSaturationResolution, csplRegularResolution


# Refutationally Complete Resolution Algorithms

@docs csplSCFResolution, csplSCFLinearResolution, csplSCFPositiveResolution, csplSCFNegativeResolution


# Non Refutationally Complete Resolution Algorithms

@docs csplSCFUnitaryResolution, csplSCFByEntriesResolution


# Resolution Tableau Representation

@docs resolutionTableauToString, resolutionTableauToDOT

-}

import Dict exposing (Dict)
import Graph exposing (Edge, Graph, Node)
import Graph.DOT exposing (defaultStyles)
import List.Extra as LE
import LogicUS.PL.NFC as PL_NFC exposing (ClausePL)
import LogicUS.PL.SintaxSemantics as PL_SS exposing (FormulaPL(..), Literal, PSymb)


{-| Defines the Resolution Tableau type as a Graph whose node labels are pairs of a bool (indicates if the node is in the original clause set (True) or is a deduction (False)) and the clause considered in the corresponding node; and a edge label is just the literal of source node which is considered in the resolvent.
-}
type alias ResolutionTableau =
    Graph ( Bool, ClausePL ) Literal


type alias ResolutionItem =
    { c : ClausePL
    , p1 : Int
    , l1 : Literal
    , p2 : Int
    , l2 : Literal
    }



--===========--
-- FUNCTIONS --
--===========--
--------------------
-- Aux. Functions --
--------------------
-- It concatenates two lists omitting elements from the second that are alredy in first one.


uniqueConcatList : List a -> List a -> List a
uniqueConcatList xs ys =
    List.foldl
        (\y ac ->
            if List.member y ac then
                ac

            else
                ac ++ [ y ]
        )
        xs
        ys


csplConcat : List ClausePL -> List ClausePL -> List ClausePL
csplConcat xs ys =
    List.foldl
        (\y ac ->
            if List.any (\x -> PL_NFC.cplEqClauses x y) ac then
                ac

            else
                ac ++ [ y ]
        )
        xs
        ys



-- It gives the variable of literal


literalSymbol : Literal -> String
literalSymbol l =
    case l of
        Atom psymb ->
            psymb

        Neg (Atom psymb) ->
            psymb

        _ ->
            ""



-- It removes the resolution items whose clause is subsumed by other of other item.


filterSubsumedResolutionItems : List ResolutionItem -> List ResolutionItem
filterSubsumedResolutionItems xs =
    List.foldl
        (\x ac ->
            if List.any (\y -> PL_NFC.cplSubsumes y.c x.c) ac then
                ac

            else
                ac ++ [ x ]
        )
        []
        (List.sortBy (\x -> List.length x.c) xs)



-----------------------
--  Module Functions --
-----------------------


{-| It gets the resolvent from two clauses by one literal. If it can be performed then it returns the resolvent and the literal considerated in each clause. If the resolvent does not exist it returns Nothing.

    cplResolventByPSymb [ Atom "p", Atom "q" ] [ Neg (Atom "p"), Atom "q" ] "p" == Just ( [ Atom "q" ], Atom "p", Neg (Atom "p") )

    cplResolventByPSymb [ Atom "p", Atom "q" ] [ Neg (Atom "p"), Atom "q" ] "q" == Nothing

-}
cplResolventByPSymb : ClausePL -> ClausePL -> PSymb -> Maybe ( ClausePL, Literal, Literal )
cplResolventByPSymb c1 c2 v =
    if List.member (Atom v) c1 && List.member (Neg (Atom v)) c2 then
        Just <|
            ( List.sortBy PL_SS.fplSymbols <| uniqueConcatList [] <| List.filter (\x -> x /= Atom v) c1 ++ List.filter (\x -> x /= Neg (Atom v)) c2
            , Atom v
            , Neg (Atom v)
            )

    else if List.member (Atom v) c2 && List.member (Neg (Atom v)) c1 then
        Just <|
            ( List.sortBy PL_SS.fplSymbols <| uniqueConcatList [] <| List.filter (\x -> x /= Neg (Atom v)) c1 ++ List.filter (\x -> x /= Atom v) c2
            , Neg (Atom v)
            , Atom v
            )

    else
        Nothing


{-| It gets all passible resolvents between two clauses. Note that if several resolvents can be performed then all of them are tautologies.

    cplAllResolvents [ Atom "p", Atom "q" ] [ Neg (Atom "p"), Neg (Atom "q") ] = cplAllResolvents  [ Atom "p", Atom "q" ] [ Neg (Atom "p"), (Neg Atom "q") ]

    cplAllResolvents [ Atom "p", Atom "q" ] [ Neg (Atom "p"), Atom "q" ] == [([Atom "q"],Atom "p",Neg (Atom "p"))]

    cplAllResolvents [ Atom "p", Atom "q" ] [ Atom "p" ] == []

-}
cplAllResolvents : ClausePL -> ClausePL -> List ( ClausePL, Literal, Literal )
cplAllResolvents c1 c2 =
    List.foldl
        (\l ac ->
            case cplResolventByPSymb c1 c2 (literalSymbol l) of
                Nothing ->
                    ac

                Just r ->
                    uniqueConcatList ac [ r ]
        )
        []
        c1


{-| It gets the resolvents between the clauses of a set by the variable given.

    csplAllResolventsByPsymb [ [ Atom "p", Atom "q" ], [ Neg (Atom "p"), Neg (Atom "q") ], [ Neg (Atom "p"), Atom "q" ] ] "p"
        == [ [ Atom "q", Neg (Atom "q") ], [ Atom "q" ] ]

-}
csplAllResolventsByPsymb : List ClausePL -> PSymb -> List ClausePL
csplAllResolventsByPsymb cs v =
    Tuple.second <|
        List.foldl
            (\c2 ( cs_, res ) ->
                let
                    rs_c2 =
                        List.foldl
                            (\c1 ac ->
                                case cplResolventByPSymb c1 c2 v of
                                    Nothing ->
                                        ac

                                    Just ( cr, _, _ ) ->
                                        ac ++ [ cr ]
                            )
                            []
                            cs_
                in
                ( cs_ ++ [ c2 ], csplConcat res rs_c2 )
            )
            ( [], [] )
            cs


{-| It gets all resolvents of each clause of a set with a clause given. It returns a list of a pair with the index of the formula with which the reference clause is resolved and all the resolvents obtained.

    csplResolventsByClause [ [ Atom "p", Atom "q" ], [ Neg (Atom "p"), Neg (Atom "q") ] ] [ Neg (Atom "p"), Atom "q" ]
        == [ ( 0, [ ( [ Atom "q" ], Neg (Atom "p"), Atom "p" ) ] ), ( 1, [ ( [ Neg (Atom "p") ], Atom "q", Neg (Atom "q") ) ] ) ]

-}
csplResolventsByClause : List ClausePL -> ClausePL -> List ( Int, List ( ClausePL, Literal, Literal ) )
csplResolventsByClause cs c =
    List.indexedMap
        (\i ci ->
            ( i
            , cplAllResolvents c ci
            )
        )
        cs


{-| It gets all possible resolvents each two clauses of the set, and gives it as a clause set ommitting who are the parents and removing duplicated clauses.

    csplAllResolvents [ [ Atom "p", Atom "q" ], [ Neg (Atom "p"), Neg (Atom "q") ], [ Neg (Atom "p"), Atom "q" ] ]
        == [ [ Neg (Atom "q"), Atom "q" ], [ Neg (Atom "p"), Atom "p" ], [ Atom "q" ], [ Neg (Atom "p") ] ]

-}
csplAllResolvents : List ClausePL -> List ClausePL
csplAllResolvents cs =
    Tuple.second <|
        List.foldl
            (\c ( prev, ac ) ->
                let
                    ri =
                        List.map (\( x, _, _ ) -> x) <| List.concat <| List.map (\c2 -> cplAllResolvents c c2) prev
                in
                ( prev ++ [ c ], csplConcat ac ri )
            )
            ( [], [] )
            cs



--===========================
--== SATURATION RESOLUTION ==
--===========================


{-| It uses saturation resolution algorithm for determining the feasibilibity of a set ot clauses. It gives the insatisfactibility (True:Insat, False:SAT) and the clause set considerated in each step of the algorithm.

    cs = [[Neg (Atom "p"),Neg (Atom "q"),Atom "r"],[Atom "q",Atom "p"],[Neg (Atom "r"),Atom "p"],[Neg (Atom "p"),Atom "q"],[Neg (Atom "q"),Atom "p"],[Neg (Atom "p"),Neg (Atom "r")]]


    csplAllResolvents cs
        == (True,[[[Neg (Atom "p"),Neg (Atom "q"),Atom "r"],[Atom "q",Atom "p"],[Neg (Atom "r"),Atom "p"],[Neg (Atom "p"),Atom "q"],[Neg (Atom "q"),Atom "p"],[Neg (Atom "p"),Neg (Atom "r")],[Atom "p",Neg (Atom "p"),Atom "r"],[Atom "q",Neg (Atom "q"),Atom "r"],[Atom "p",Neg (Atom "p"),Neg (Atom "q")],[Neg (Atom "q"),Neg (Atom "r"),Atom "r"],[Neg (Atom "p"),Atom "r"],[Atom "q"],...)

-}
csplSaturationResolution : List ClausePL -> ( Bool, List (List ClausePL) )
csplSaturationResolution cs =
    csplSaturationResolutionAux cs []



-- It perfomes saturation resolution algorithm


csplSaturationResolutionAux : List ClausePL -> List (List ClausePL) -> ( Bool, List (List ClausePL) )
csplSaturationResolutionAux cs hist =
    if List.any List.isEmpty cs then
        ( True, hist )

    else
        let
            cs2 =
                csplAllResolvents cs
        in
        if List.isEmpty cs2 then
            ( False, hist ++ [ cs ] )

        else
            csplSaturationResolutionAux (cs ++ cs2) (hist ++ [ cs ++ cs2 ])



--========================
--== REGULAR RESOLUTION ==
--========================


{-| It uses regular resolution algorithm for determining the feasibilibity of a set ot clauses. It gives the insatisfactibility (True:Insat, False:SAT) and the clause set considerated in each step of the algorithm.

    csplRegularResolution [ "p", "q", "r" ] cs
        == ( True, [ [ [ Neg (Atom "p"), Neg (Atom "q"), Atom "r" ], [ Atom "q", Atom "p" ], [ Neg (Atom "r"), Atom "p" ], [ Neg (Atom "p"), Atom "q" ], [ Neg (Atom "q"), Atom "p" ], [ Neg (Atom "p"), Neg (Atom "r") ] ], [ [ Neg (Atom "q"), Atom "q", Atom "r" ], [ Neg (Atom "q"), Atom "r", Neg (Atom "r") ], [ Atom "q" ], [ Atom "q", Neg (Atom "r") ], [ Neg (Atom "q"), Atom "r" ], [ Atom "q", Neg (Atom "q") ], [ Neg (Atom "r") ], [ Neg (Atom "q"), Neg (Atom "r") ] ], [ [ Neg (Atom "r") ], [ Atom "r", Neg (Atom "r") ], [ Atom "r" ], [ Neg (Atom "r") ] ], [ [] ] ] )

-}
csplRegularResolution : List PSymb -> List ClausePL -> ( Bool, List (List ClausePL) )
csplRegularResolution vars cs =
    let
        res =
            List.foldl
                (\v ( hist, s ) ->
                    let
                        s_ =
                            List.filter (\c -> not <| List.member (Atom v) c || List.member (Neg (Atom v)) c) <| s ++ csplAllResolventsByPsymb s v
                    in
                    ( hist ++ [ s_ ], s_ )
                )
                ( [ cs ], cs )
                vars
    in
    ( not <| List.isEmpty <| Tuple.second res, Tuple.first res )



--===========================
--== RESOLUTION STRATEGIES ==
--===========================
-- It extracts the path (nodes and edges) to a resolution item in the following resolution algorithms.


recoverResolutionPathAux : Int -> Dict Int ResolutionItem -> ( List (Node ClausePL), List (Edge Literal) )
recoverResolutionPathAux i refDict =
    case Dict.get i refDict of
        Just ri ->
            let
                ( nodes1, edges1 ) =
                    recoverResolutionPathAux ri.p1 refDict

                ( nodes2, edges2 ) =
                    recoverResolutionPathAux ri.p2 refDict
            in
            ( uniqueConcatList nodes1 nodes2 ++ [ Node i ri.c ]
            , uniqueConcatList edges1 edges2 ++ [ Edge ri.p1 i ri.l1, Edge ri.p2 i ri.l2 ]
            )

        _ ->
            ( [], [] )



--=======================
--== COMMON RESOLUTION ==
--=======================
-- It gets the resolvents of one clause and the closed (explored) clauses


resolventsWithClosedSCFResolutionAux : List ( Int, ResolutionItem ) -> Int -> ClausePL -> List ResolutionItem
resolventsWithClosedSCFResolutionAux closed id c =
    List.foldl
        (\( i, ri ) ac ->
            let
                resolvents_i =
                    cplAllResolvents c ri.c
            in
            let
                accepted =
                    (PL_NFC.csplRemoveSubsumedClauses << PL_NFC.csplRemoveTautClauses) <| List.map (\( f, _, _ ) -> f) resolvents_i
            in
            ac
                ++ (Tuple.first <|
                        List.foldl
                            (\( cj, l1, l2 ) ( ac2, acc ) ->
                                if List.member cj acc then
                                    if not <| List.any (\x -> PL_NFC.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_NFC.cplSubsumes x.c cj) closed then
                                        ( ac2 ++ [ { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } ]
                                        , List.filter (\x -> x /= cj) acc
                                        )

                                    else
                                        ( ac2
                                        , List.filter (\x -> x /= cj) acc
                                        )

                                else
                                    ( ac2, acc )
                            )
                            ( [], accepted )
                            resolvents_i
                   )
        )
        []
        closed



-- It updates the list of opened (unexplored) clauses given it as a pair whose first component corresponds to length (heuristic) of the clause and the second one to the clause properly.


openedUpdationSCFResolutionAux : List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem )
openedUpdationSCFResolutionAux xs new_opens =
    let
        res =
            List.foldl
                (\( li, ri ) ( ac, rest ) ->
                    let
                        add_ac =
                            LE.takeWhile (\( lx, _ ) -> lx <= li) rest
                    in
                    if List.any (\( _, x ) -> PL_NFC.cplSubsumes x.c ri.c) (ac ++ add_ac) then
                        ( ac ++ add_ac, List.drop (List.length add_ac) rest )

                    else
                        ( ac ++ add_ac ++ [ ( li, ri ) ]
                        , List.filter (\( _, x ) -> not (PL_NFC.cplSubsumes ri.c x.c)) <| List.drop (List.length add_ac) rest
                        )
                )
                ( [], xs )
                new_opens
    in
    Tuple.first res ++ Tuple.second res



-- It performs the resolution algoritm with only Shortest Clause First heuristic.


csplSCFResolutionAux : List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem ) -> Int -> ( List (Node ClausePL), List (Edge Literal) )
csplSCFResolutionAux closed opened nid =
    case opened of
        [] ->
            ( [], [] )

        ( _, ri ) :: xs ->
            if List.isEmpty ri.c then
                let
                    refDict =
                        Dict.fromList <| closed ++ [ ( nid + 1, ri ) ]
                in
                recoverResolutionPathAux (nid + 1) refDict

            else
                let
                    r_closed =
                        resolventsWithClosedSCFResolutionAux closed (nid + 1) ri.c
                in
                let
                    new_closed =
                        closed ++ [ ( nid + 1, ri ) ]

                    new_opened =
                        openedUpdationSCFResolutionAux xs (List.sortBy (\x -> Tuple.first x) <| List.map (\x -> ( List.length x.c, x )) r_closed)
                in
                csplSCFResolutionAux new_closed new_opened (nid + 1)


{-| It uses resolution algorithm using shortes clause first heuristic for determining the feasibilibity of a set of clauses. It gives the insatisfactibility (True:Insat, False:SAT) and a graph with the resolution path to inconsitence. If clause set is feasible then a graph with only initial nodes is returned.

    res_SCFResolution = csplSCFResolution cs

    Tuple.first res_SCFResolution == True

    res_SCFResolution |> Tuple.second |> resolutionTableauToDOT
        == "digraph G {\n  rankdir=TB\n  graph []\n  node [shape=box, color=black]\n  edge [dir=none, color=blue, fontcolor=blue]\n\n  1 -> 6 [label=\"q\"]\n  2 -> 8 [label=\"p\"]\n  3 -> 10 [label=\"q\"]\n  5 -> 6 [label=\"¬ q\"]\n  6 -> 11 [label=\"p\"]\n  7 -> 8 [label=\"¬ p\"]\n  8 -> 12 [label=\"¬ r\"]\n  9 -> 10 [label=\"¬ q\"]\n  10 -> 11 [label=\"¬ p\"]\n  11 -> 12 [label=\"r\"]\n\n  1 [label=\"{q, p}\"]\n  2 [label=\"{¬ r, p}\"]\n  3 [label=\"{¬ p, q}\"]\n  5 [label=\"{¬ q, p}\"]\n  6 [label=\"{p}\"]\n  7 [label=\"{¬ p, ¬ r}\"]\n  8 [label=\"{¬ r}\"]\n  9 [label=\"{¬ p, ¬ q, r}\"]\n  10 [label=\"{¬ p, r}\"]\n  11 [label=\"{r}\"]\n  12 [label=\"□\"]\n\n  {rank=same; 1;2;3;5;7;9;}\n}"

Note: You can render the graph with GraphViz Viewer and _resolutionTableauToDOt_ as we show in the example above.

-}
csplSCFResolution : List ClausePL -> ( Bool, ResolutionTableau )
csplSCFResolution cs =
    let
        new_cs =
            List.sortBy (\x -> Tuple.first x) <| List.map (\x -> ( List.length x, { c = x, p1 = 0, p2 = 0, l1 = Atom "", l2 = Atom "" } )) <| PL_NFC.csplRemoveSubsumedClauses <| PL_NFC.csplRemoveTautClauses <| cs
    in
    let
        ( nodes, edges ) =
            csplSCFResolutionAux [] new_cs 0
    in
    let
        nid_max =
            Maybe.withDefault 0 <| List.maximum <| List.map (\x -> x.id) <| nodes

        nodes_clauses =
            List.map (\x -> x.label) <| nodes
    in
    let
        final_nodes =
            List.map (\x -> Node x.id ( List.member x.label cs, x.label )) nodes
                ++ (List.indexedMap (\i x -> Node (nid_max + i + 1) ( True, x )) <| List.filter (\x -> not (List.member x nodes_clauses)) cs)
    in
    ( edges /= [], Graph.fromNodesAndEdges final_nodes edges )



--=======================
--== LINEAR RESOLUTION ==
--=======================
-- It calculates the resolvents with closed clauses


resolventsWithClosedSCFLinearResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> Int -> ClausePL -> List ResolutionItem
resolventsWithClosedSCFLinearResolutionAux closed resDone id c =
    List.sortBy (\x -> List.length x.c) <|
        List.foldl
            (\( i, ri ) ac ->
                if List.member id <| Maybe.withDefault [] <| Dict.get i resDone then
                    ac

                else
                    let
                        resolvents_i =
                            List.filter (\( cj, _, _ ) -> not <| PL_NFC.cplIsTautology cj) <| cplAllResolvents c ri.c
                    in
                    List.foldl
                        (\( cj, l1, l2 ) ac2 ->
                            if not <| (List.any (\x -> PL_NFC.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_NFC.cplSubsumes x.c cj) closed) then
                                List.filter (\x -> not <| PL_NFC.cplSubsumes cj x.c) ac2 ++ [ { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } ]

                            else
                                ac2
                        )
                        ac
                        resolvents_i
            )
            []
            closed



-- It calculates the resolvents with opened clauses


resolventsWithOpenedSCFLinearResolutionAux : List ( Int, ResolutionItem ) -> Int -> ClausePL -> List ResolutionItem
resolventsWithOpenedSCFLinearResolutionAux opened id c =
    List.sortBy (\x -> List.length x.c) <|
        List.foldl
            (\( i, ri ) ac ->
                let
                    resolvents_i =
                        List.filter (\( cj, _, _ ) -> not <| PL_NFC.cplIsTautology cj) <| cplAllResolvents c ri.c
                in
                List.foldl
                    (\( cj, l1, l2 ) ac2 ->
                        if not <| List.any (\x -> PL_NFC.cplSubsumes x.c cj) ac then
                            List.filter (\x -> not <| PL_NFC.cplSubsumes cj x.c) ac2 ++ [ { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } ]

                        else
                            ac2
                    )
                    ac
                    resolvents_i
            )
            []
            opened



-- It performs the linear resolution algorithm with SCF heuristic


csplSCFLinearResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> List ( Int, ResolutionItem ) -> Int -> ( List (Node ClausePL), List (Edge Literal) )
csplSCFLinearResolutionAux closed resDone opened nid =
    case opened of
        [] ->
            ( [], [] )

        ( id, rid ) :: xs ->
            if List.isEmpty rid.c then
                let
                    refDict =
                        Dict.fromList <| closed ++ opened
                in
                recoverResolutionPathAux id refDict

            else
                let
                    resolvents_i =
                        filterSubsumedResolutionItems <|
                            List.sortBy (\x -> List.length x.c) <|
                                resolventsWithClosedSCFLinearResolutionAux closed resDone id rid.c
                                    ++ (List.filter (\ri -> not <| List.any (\( _, x ) -> PL_NFC.cplSubsumes x.c ri.c) closed) <| resolventsWithOpenedSCFLinearResolutionAux xs id rid.c)
                in
                let
                    newClosed =
                        closed ++ [ ( id, rid ) ]

                    newResDone =
                        Dict.insert id (List.map Tuple.first <| closed ++ xs) <| Dict.map (\_ v -> v ++ [ id ]) resDone
                in
                List.foldl
                    (\ri result ->
                        if List.isEmpty <| Tuple.first result then
                            let
                                res_i =
                                    csplSCFLinearResolutionAux newClosed newResDone (( nid + 1, ri ) :: xs) (nid + 1)
                            in
                            res_i

                        else
                            result
                    )
                    ( [], [] )
                    resolvents_i


{-| It uses linear resolution algorithm using shortest clause first heuristic for determining the feasibilibity of a set of clauses. It gives the insatisfactibility (True:Insat, False:SAT) and a graph with the resolution path to inconsitence. If clause set is feasible then a graph with only initial nodes is returned.

    res_SCFLinearResolution = csplSCFLinearResolution cs

    Tuple.first res_SCFLinearResolution == True

    res_SCFLinearResolution |> Tuple.second |> resolutionTableauToDOT
        == "digraph G {\n  rankdir=TB\n  graph []\n  node [shape=box, color=black]\n  edge [dir=none, color=blue, fontcolor=blue]\n\n  1 -> 8 [label=\"p\"]\n  3 -> 8 [label=\"¬ p\"]\n  4 -> 9 [label=\"¬ q\"]\n  5 -> 10 [label=\"¬ p\"]\n  6 -> 11 [label=\"r\"]\n  8 -> 9 [label=\"q\"]\n  8 -> 12 [label=\"q\"]\n  9 -> 10 [label=\"p\"]\n  9 -> 13 [label=\"p\"]\n  10 -> 11 [label=\"¬ r\"]\n  11 -> 12 [label=\"¬ q\"]\n  12 -> 13 [label=\"¬ p\"]\n\n  1 [label=\"{q, p}\"]\n  3 [label=\"{¬ p, q}\"]\n  4 [label=\"{¬ q, p}\"]\n  5 [label=\"{¬ p, ¬ r}\"]\n  6 [label=\"{¬ p, ¬ q, r}\"]\n  8 [label=\"{q}\"]\n  9 [label=\"{p}\"]\n  10 [label=\"{¬ r}\"]\n  11 [label=\"{¬ p, ¬ q}\"]\n  12 [label=\"{¬ p}\"]\n  13 [label=\"□\"]\n  14 [label=\"{¬ r, p}\"]\n\n  {rank=same; 1;3;4;5;6;14;}\n}"

Note: You can render the graph with GraphViz Viewer and _resolutionTableauToDOT_ described at the end.

-}
csplSCFLinearResolution : List ClausePL -> ( Bool, ResolutionTableau )
csplSCFLinearResolution cs =
    let
        new_cs =
            List.indexedMap (\i x -> ( i + 1, { c = x, p1 = 0, p2 = 0, l1 = Atom "", l2 = Atom "" } )) <| List.sortBy (\x -> List.length x) <| PL_NFC.csplRemoveSubsumedClauses <| PL_NFC.csplRemoveTautClauses <| cs
    in
    let
        ( nodes, edges ) =
            csplSCFLinearResolutionAux [] Dict.empty new_cs (List.length new_cs + 1)
    in
    -- ( nodes, edges )
    let
        nid_max =
            Maybe.withDefault 0 <| List.maximum <| List.map (\x -> x.id) <| nodes

        nodes_clauses =
            List.map (\x -> x.label) <| nodes
    in
    let
        final_nodes =
            List.map (\x -> Node x.id ( List.member x.label cs, x.label )) nodes
                ++ (List.indexedMap (\i x -> Node (nid_max + i + 1) ( True, x )) <| List.filter (\x -> not (List.member x nodes_clauses)) cs)
    in
    ( edges /= [], Graph.fromNodesAndEdges final_nodes edges )



--=========================
--== POSITIVE RESOLUTION ==
--=========================


openedUpdationSCFPositiveResolutionAux : List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem )
openedUpdationSCFPositiveResolutionAux xs new_opens =
    let
        res =
            List.foldl
                (\( li, ri ) ( ac, rest ) ->
                    let
                        add_ac =
                            LE.takeWhile (\( _, x ) -> List.length x.c <= List.length ri.c) rest
                    in
                    if List.any (\( _, x ) -> PL_NFC.cplSubsumes x.c ri.c) (ac ++ add_ac) then
                        ( ac ++ add_ac, List.drop (List.length add_ac) rest )

                    else
                        ( ac ++ add_ac ++ [ ( li, ri ) ]
                        , List.drop (List.length add_ac) rest
                        )
                )
                ( [], xs )
                new_opens
    in
    Tuple.first res ++ Tuple.second res


resolventsWithClosedSCFPositiveResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> Int -> ClausePL -> List ResolutionItem
resolventsWithClosedSCFPositiveResolutionAux closed resDone id c =
    List.sortBy (\x -> List.length x.c) <|
        List.foldl
            (\( i, ri ) ac ->
                if (List.member id <| Maybe.withDefault [] <| Dict.get i resDone) || not (PL_NFC.cplIsPositive c || PL_NFC.cplIsPositive ri.c) then
                    ac

                else
                    let
                        resolvents_i =
                            List.filter (\( cj, _, _ ) -> not <| PL_NFC.cplIsTautology cj) <| cplAllResolvents c ri.c
                    in
                    List.foldl
                        (\( cj, l1, l2 ) ac2 ->
                            if not <| (List.any (\x -> PL_NFC.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_NFC.cplSubsumes x.c cj) closed) then
                                List.filter (\x -> not <| PL_NFC.cplSubsumes cj x.c) ac2 ++ [ { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } ]

                            else
                                ac2
                        )
                        ac
                        resolvents_i
            )
            []
            closed


resolventsWithOpenedSCFPositiveResolutionAux : List ( Int, ResolutionItem ) -> Int -> ClausePL -> List ResolutionItem
resolventsWithOpenedSCFPositiveResolutionAux opened id c =
    List.sortBy (\x -> List.length x.c) <|
        List.foldl
            (\( i, ri ) ac ->
                if not (PL_NFC.cplIsPositive c || PL_NFC.cplIsPositive ri.c) then
                    ac

                else
                    let
                        resolvents_i =
                            List.filter (\( cj, _, _ ) -> not <| PL_NFC.cplIsTautology cj) <| cplAllResolvents c ri.c
                    in
                    List.foldl
                        (\( cj, l1, l2 ) ac2 ->
                            if not <| List.any (\x -> PL_NFC.cplSubsumes x.c cj) ac then
                                List.filter (\x -> not <| PL_NFC.cplSubsumes cj x.c) ac2 ++ [ { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } ]

                            else
                                ac2
                        )
                        ac
                        resolvents_i
            )
            []
            opened


csplSCFPositiveResolutionAux : List ( Int, { c : ClausePL, p1 : Int, l1 : Literal, p2 : Int, l2 : Literal } ) -> Dict Int (List Int) -> List ( Int, { c : ClausePL, p1 : Int, l1 : Literal, p2 : Int, l2 : Literal } ) -> Int -> ( List (Node ClausePL), List (Edge Literal) )
csplSCFPositiveResolutionAux closed resDone opened nid =
    case opened of
        [] ->
            ( [], [] )

        ( id, rid ) :: xs ->
            if List.isEmpty rid.c then
                let
                    refDict =
                        Dict.fromList <| closed ++ opened
                in
                recoverResolutionPathAux id refDict

            else
                let
                    resolvents_i =
                        List.indexedMap (\i x -> ( nid + i + 1, x )) <|
                            filterSubsumedResolutionItems <|
                                List.sortBy (\x -> List.length x.c) <|
                                    resolventsWithClosedSCFPositiveResolutionAux closed resDone id rid.c
                                        ++ (List.filter (\ri -> not <| List.any (\( _, x ) -> PL_NFC.cplSubsumes x.c ri.c) closed) <| resolventsWithOpenedSCFPositiveResolutionAux xs id rid.c)
                in
                let
                    new_closed =
                        closed ++ [ ( id, rid ) ]

                    newResDone =
                        Dict.insert id (List.map Tuple.first (closed ++ xs)) <| Dict.map (\_ v -> v ++ [ id ]) resDone

                    new_opened =
                        openedUpdationSCFPositiveResolutionAux xs resolvents_i
                in
                csplSCFPositiveResolutionAux new_closed newResDone new_opened (nid + List.length resolvents_i + 1)


{-| It uses positive resolution algorithm using shortest clause first heuristic for determining the feasibilibity of a set of clauses. It gives the insatisfactibility (True:Insat, False:SAT) and a graph with the resolution path to inconsitence. If clause set is feasible then a graph with only initial nodes is returned.

    res_SCFPositiveResolution = csplSCFPositiveResolution cs

    Tuple.first res_SCFPositiveResolution == True

    res_SCFPositiveResolution |> Tuple.second |> resolutionTableauToDOT
        == "digraph G {\n  rankdir=TB\n  graph []\n  node [shape=box, color=black]\n  edge [dir=none, color=blue, fontcolor=blue]\n\n  1 -> 8 [label=\"p\"]\n  1 -> 9 [label=\"q\"]\n  3 -> 8 [label=\"¬ p\"]\n  4 -> 9 [label=\"¬ q\"]\n  5 -> 14 [label=\"¬ p\"]\n  6 -> 12 [label=\"¬ q\"]\n  8 -> 12 [label=\"q\"]\n  9 -> 14 [label=\"p\"]\n  9 -> 15 [label=\"p\"]\n  12 -> 15 [label=\"¬ p\"]\n  14 -> 17 [label=\"¬ r\"]\n  15 -> 17 [label=\"r\"]\n\n  1 [label=\"{q, p}\"]\n  3 [label=\"{¬ p, q}\"]\n  4 [label=\"{¬ q, p}\"]\n  5 [label=\"{¬ p, ¬ r}\"]\n  6 [label=\"{¬ p, ¬ q, r}\"]\n  8 [label=\"{q}\"]\n  9 [label=\"{p}\"]\n  12 [label=\"{¬ p, r}\"]\n  14 [label=\"{¬ r}\"]\n  15 [label=\"{r}\"]\n  17 [label=\"□\"]\n  18 [label=\"{¬ r, p}\"]\n\n  {rank=same; 1;3;4;5;6;18;}\n}"

Note: You can render the graph with GraphViz Viewer and _resolutionTableauToDOT_ described at the end.

-}
csplSCFPositiveResolution : List ClausePL -> ( Bool, Graph ( Bool, ClausePL ) Literal )
csplSCFPositiveResolution cs =
    let
        new_cs =
            List.indexedMap (\i x -> ( i + 1, { c = x, p1 = 0, p2 = 0, l1 = Atom "", l2 = Atom "" } )) <| List.sortBy (\x -> List.length x) <| PL_NFC.csplRemoveSubsumedClauses <| PL_NFC.csplRemoveTautClauses <| cs
    in
    let
        ( nodes, edges ) =
            csplSCFPositiveResolutionAux [] Dict.empty new_cs (List.length new_cs + 1)
    in
    let
        nid_max =
            Maybe.withDefault 0 <| List.maximum <| List.map (\x -> x.id) <| nodes

        nodes_clauses =
            List.map (\x -> x.label) <| nodes
    in
    let
        final_nodes =
            List.map (\x -> Node x.id ( List.member x.label cs, x.label )) nodes
                ++ (List.indexedMap (\i x -> Node (nid_max + i + 1) ( True, x )) <| List.filter (\x -> not (List.member x nodes_clauses)) cs)
    in
    ( edges /= [], Graph.fromNodesAndEdges final_nodes edges )



--=========================
--== NEGATIVE RESOLUTION ==
--=========================


openedUpdationSCFNegativeResolutionAux : List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem )
openedUpdationSCFNegativeResolutionAux xs new_opens =
    let
        res =
            List.foldl
                (\( li, ri ) ( ac, rest ) ->
                    let
                        add_ac =
                            LE.takeWhile (\( _, x ) -> List.length x.c <= List.length ri.c) rest
                    in
                    if List.any (\( _, x ) -> PL_NFC.cplSubsumes x.c ri.c) (ac ++ add_ac) then
                        ( ac ++ add_ac, List.drop (List.length add_ac) rest )

                    else
                        ( ac ++ add_ac ++ [ ( li, ri ) ]
                        , List.drop (List.length add_ac) rest
                        )
                )
                ( [], xs )
                new_opens
    in
    Tuple.first res ++ Tuple.second res


resolventsWithClosedSCFNegativeResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> Int -> ClausePL -> List ResolutionItem
resolventsWithClosedSCFNegativeResolutionAux closed resDone id c =
    List.sortBy (\x -> List.length x.c) <|
        List.foldl
            (\( i, ri ) ac ->
                if (List.member id <| Maybe.withDefault [] <| Dict.get i resDone) || not (PL_NFC.cplIsNegative c || PL_NFC.cplIsNegative ri.c) then
                    ac

                else
                    let
                        resolvents_i =
                            List.filter (\( cj, _, _ ) -> not <| PL_NFC.cplIsTautology cj) <| cplAllResolvents c ri.c
                    in
                    List.foldl
                        (\( cj, l1, l2 ) ac2 ->
                            if not <| (List.any (\x -> PL_NFC.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_NFC.cplSubsumes x.c cj) closed) then
                                List.filter (\x -> not <| PL_NFC.cplSubsumes cj x.c) ac2 ++ [ { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } ]

                            else
                                ac2
                        )
                        ac
                        resolvents_i
            )
            []
            closed


resolventsWithOpenedSCFNegativeResolutionAux : List ( Int, ResolutionItem ) -> Int -> ClausePL -> List ResolutionItem
resolventsWithOpenedSCFNegativeResolutionAux opened id c =
    List.sortBy (\x -> List.length x.c) <|
        List.foldl
            (\( i, ri ) ac ->
                if not (PL_NFC.cplIsNegative c || PL_NFC.cplIsNegative ri.c) then
                    ac

                else
                    let
                        resolvents_i =
                            List.filter (\( cj, _, _ ) -> not <| PL_NFC.cplIsTautology cj) <| cplAllResolvents c ri.c
                    in
                    List.foldl
                        (\( cj, l1, l2 ) ac2 ->
                            if not <| List.any (\x -> PL_NFC.cplSubsumes x.c cj) ac then
                                List.filter (\x -> not <| PL_NFC.cplSubsumes cj x.c) ac2 ++ [ { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } ]

                            else
                                ac2
                        )
                        ac
                        resolvents_i
            )
            []
            opened


csplSCFNegativeResolutionAux : List ( Int, { c : ClausePL, p1 : Int, l1 : Literal, p2 : Int, l2 : Literal } ) -> Dict Int (List Int) -> List ( Int, { c : ClausePL, p1 : Int, l1 : Literal, p2 : Int, l2 : Literal } ) -> Int -> ( List (Node ClausePL), List (Edge Literal) )
csplSCFNegativeResolutionAux closed resDone opened nid =
    case opened of
        [] ->
            ( [], [] )

        ( id, rid ) :: xs ->
            if List.isEmpty rid.c then
                let
                    refDict =
                        Dict.fromList <| closed ++ opened
                in
                recoverResolutionPathAux id refDict

            else
                let
                    resolvents_i =
                        List.indexedMap (\i x -> ( nid + i + 1, x )) <|
                            filterSubsumedResolutionItems <|
                                List.sortBy (\x -> List.length x.c) <|
                                    resolventsWithClosedSCFNegativeResolutionAux closed resDone id rid.c
                                        ++ (List.filter (\ri -> not <| List.any (\( _, x ) -> PL_NFC.cplSubsumes x.c ri.c) closed) <| resolventsWithOpenedSCFNegativeResolutionAux xs id rid.c)
                in
                let
                    new_closed =
                        closed ++ [ ( id, rid ) ]

                    newResDone =
                        Dict.insert id (List.map Tuple.first (closed ++ xs)) <| Dict.map (\_ v -> v ++ [ id ]) resDone

                    new_opened =
                        openedUpdationSCFNegativeResolutionAux xs resolvents_i
                in
                csplSCFNegativeResolutionAux new_closed newResDone new_opened (nid + List.length resolvents_i + 1)


{-| It uses negative resolution algorithm using shortest clause first heuristic for determining the feasibilibity of a set of clauses. It gives the insatisfactibility (True:Insat, False:SAT) and a graph with the resolution path to inconsitence. If clause set is feasible then a graph with only initial nodes is returned.

    res_SCFNegativeResolution = csplSCFNegativeResolution cs

    Tuple.first res_SCFNegativeResolution == True

    res_SCFNegativeResolution |> Tuple.second |> resolutionTableauToDOT
        == "digraph G {\n  rankdir=TB\n  graph []\n  node [shape=box, color=black]\n  edge [dir=none, color=blue, fontcolor=blue]\n\n  1 -> 16 [label=\"p\"]\n  2 -> 10 [label=\"p\"]\n  3 -> 14 [label=\"q\"]\n  4 -> 17 [label=\"p\"]\n  5 -> 10 [label=\"¬ p\"]\n  6 -> 12 [label=\"r\"]\n  10 -> 12 [label=\"¬ r\"]\n  12 -> 14 [label=\"¬ q\"]\n  14 -> 16 [label=\"¬ p\"]\n  14 -> 17 [label=\"¬ p\"]\n  16 -> 19 [label=\"q\"]\n  17 -> 19 [label=\"¬ q\"]\n\n  1 [label=\"{q, p}\"]\n  2 [label=\"{¬ r, p}\"]\n  3 [label=\"{¬ p, q}\"]\n  4 [label=\"{¬ q, p}\"]\n  5 [label=\"{¬ p, ¬ r}\"]\n  6 [label=\"{¬ p, ¬ q, r}\"]\n  10 [label=\"{¬ r}\"]\n  12 [label=\"{¬ p, ¬ q}\"]\n  14 [label=\"{¬ p}\"]\n  16 [label=\"{q}\"]\n  17 [label=\"{¬ q}\"]\n  19 [label=\"□\"]\n\n  {rank=same; 1;2;3;4;5;6;}\n}"

Note: You can render the graph with GraphViz Viewer and _resolutionTableauToDOT_ described at the end.

-}
csplSCFNegativeResolution : List ClausePL -> ( Bool, Graph ( Bool, ClausePL ) Literal )
csplSCFNegativeResolution cs =
    let
        new_cs =
            List.indexedMap (\i x -> ( i + 1, { c = x, p1 = 0, p2 = 0, l1 = Atom "", l2 = Atom "" } )) <| List.sortBy (\x -> List.length x) <| PL_NFC.csplRemoveSubsumedClauses <| PL_NFC.csplRemoveTautClauses <| cs
    in
    let
        ( nodes, edges ) =
            csplSCFNegativeResolutionAux [] Dict.empty new_cs (List.length new_cs + 1)
    in
    let
        nid_max =
            Maybe.withDefault 0 <| List.maximum <| List.map (\x -> x.id) <| nodes

        nodes_clauses =
            List.map (\x -> x.label) <| nodes
    in
    let
        final_nodes =
            List.map (\x -> Node x.id ( List.member x.label cs, x.label )) nodes
                ++ (List.indexedMap (\i x -> Node (nid_max + i + 1) ( True, x )) <| List.filter (\x -> not (List.member x nodes_clauses)) cs)
    in
    ( edges /= [], Graph.fromNodesAndEdges final_nodes edges )



--========================
--== UNITARY RESOLUTION ==
--========================


openedUpdationSCFUnitaryResolutionAux : List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem )
openedUpdationSCFUnitaryResolutionAux xs new_opens =
    let
        res =
            List.foldl
                (\( li, ri ) ( ac, rest ) ->
                    let
                        add_ac =
                            LE.takeWhile (\( _, x ) -> List.length x.c <= List.length ri.c) rest
                    in
                    if List.any (\( _, x ) -> PL_NFC.cplSubsumes x.c ri.c) (ac ++ add_ac) then
                        ( ac ++ add_ac, List.drop (List.length add_ac) rest )

                    else
                        ( ac ++ add_ac ++ [ ( li, ri ) ]
                        , List.drop (List.length add_ac) rest
                        )
                )
                ( [], xs )
                new_opens
    in
    Tuple.first res ++ Tuple.second res


resolventsWithClosedSCFUnitaryResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> Int -> ClausePL -> List ResolutionItem
resolventsWithClosedSCFUnitaryResolutionAux closed resDone id c =
    List.sortBy (\x -> List.length x.c) <|
        List.foldl
            (\( i, ri ) ac ->
                if (List.member id <| Maybe.withDefault [] <| Dict.get i resDone) || not (List.length c == 1 || List.length ri.c == 1) then
                    ac

                else
                    let
                        resolvents_i =
                            List.filter (\( cj, _, _ ) -> not <| PL_NFC.cplIsTautology cj) <| cplAllResolvents c ri.c
                    in
                    List.foldl
                        (\( cj, l1, l2 ) ac2 ->
                            if not <| (List.any (\x -> PL_NFC.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_NFC.cplSubsumes x.c cj) closed) then
                                List.filter (\x -> not <| PL_NFC.cplSubsumes cj x.c) ac2 ++ [ { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } ]

                            else
                                ac2
                        )
                        ac
                        resolvents_i
            )
            []
            closed


resolventsWithOpenedSCFUnitaryResolutionAux : List ( Int, ResolutionItem ) -> Int -> ClausePL -> List ResolutionItem
resolventsWithOpenedSCFUnitaryResolutionAux opened id c =
    List.sortBy (\x -> List.length x.c) <|
        List.foldl
            (\( i, ri ) ac ->
                if not (List.length c == 1 || List.length ri.c == 1) then
                    ac

                else
                    let
                        resolvents_i =
                            List.filter (\( cj, _, _ ) -> not <| PL_NFC.cplIsTautology cj) <| cplAllResolvents c ri.c
                    in
                    List.foldl
                        (\( cj, l1, l2 ) ac2 ->
                            if not <| List.any (\x -> PL_NFC.cplSubsumes x.c cj) ac then
                                List.filter (\x -> not <| PL_NFC.cplSubsumes cj x.c) ac2 ++ [ { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } ]

                            else
                                ac2
                        )
                        ac
                        resolvents_i
            )
            []
            opened


csplSCFUnitaryResolutionAux : List ( Int, { c : ClausePL, p1 : Int, l1 : Literal, p2 : Int, l2 : Literal } ) -> Dict Int (List Int) -> List ( Int, { c : ClausePL, p1 : Int, l1 : Literal, p2 : Int, l2 : Literal } ) -> Int -> ( List (Node ClausePL), List (Edge Literal) )
csplSCFUnitaryResolutionAux closed resDone opened nid =
    case opened of
        [] ->
            ( [], [] )

        ( id, rid ) :: xs ->
            if List.isEmpty rid.c then
                let
                    refDict =
                        Dict.fromList <| closed ++ opened
                in
                recoverResolutionPathAux id refDict

            else
                let
                    resolvents_i =
                        List.indexedMap (\i x -> ( nid + i + 1, x )) <|
                            filterSubsumedResolutionItems <|
                                List.sortBy (\x -> List.length x.c) <|
                                    resolventsWithClosedSCFUnitaryResolutionAux closed resDone id rid.c
                                        ++ (List.filter (\ri -> not <| List.any (\( _, x ) -> PL_NFC.cplSubsumes x.c ri.c) closed) <| resolventsWithOpenedSCFUnitaryResolutionAux xs id rid.c)
                in
                let
                    new_closed =
                        closed ++ [ ( id, rid ) ]

                    newResDone =
                        Dict.insert id (List.map Tuple.first (closed ++ xs)) <| Dict.map (\_ v -> v ++ [ id ]) resDone

                    new_opened =
                        openedUpdationSCFUnitaryResolutionAux xs resolvents_i
                in
                csplSCFUnitaryResolutionAux new_closed newResDone new_opened (nid + List.length resolvents_i + 1)


{-| It uses unitary resolution algorithm using shortest clause first heuristic for determining the feasibilibity of a set of clauses. It gives the insatisfactibility (True:Insat, False:SAT) and a graph with the resolution path to inconsitence. If clause set is feasible then a graph with only initial nodes is returned.

    res_SCFUnitaryResolution = csplSCFUnitaryResolution cs

    Tuple.first res_SCFUnitaryResolution == False

    res_SCFUnitaryResolution |> Tuple.second |> resolutionTableauToDOT
        == "digraph G {\n  rankdir=TB\n  graph []\n  node [shape=box, color=black]\n  edge [dir=none, color=blue, fontcolor=blue]\n\n\n\n  1 [label=\"{¬ p, ¬ q, r}\"]\n  2 [label=\"{q, p}\"]\n  3 [label=\"{¬ r, p}\"]\n  4 [label=\"{¬ p, q}\"]\n  5 [label=\"{¬ q, p}\"]\n  6 [label=\"{¬ p, ¬ r}\"]\n\n  {rank=same; 1;2;3;4;5;6;}\n}"

Note: You can render the graph with GraphViz Viewer and _resolutionTableauToDOT_ described at the end.

-}
csplSCFUnitaryResolution : List ClausePL -> ( Bool, Graph ( Bool, ClausePL ) Literal )
csplSCFUnitaryResolution cs =
    let
        new_cs =
            List.indexedMap (\i x -> ( i + 1, { c = x, p1 = 0, p2 = 0, l1 = Atom "", l2 = Atom "" } )) <| List.sortBy (\x -> List.length x) <| PL_NFC.csplRemoveSubsumedClauses <| PL_NFC.csplRemoveTautClauses <| cs
    in
    let
        ( nodes, edges ) =
            csplSCFUnitaryResolutionAux [] Dict.empty new_cs (List.length new_cs + 1)
    in
    let
        nid_max =
            Maybe.withDefault 0 <| List.maximum <| List.map (\x -> x.id) <| nodes

        nodes_clauses =
            List.map (\x -> x.label) <| nodes
    in
    let
        final_nodes =
            List.map (\x -> Node x.id ( List.member x.label cs, x.label )) nodes
                ++ (List.indexedMap (\i x -> Node (nid_max + i + 1) ( True, x )) <| List.filter (\x -> not (List.member x nodes_clauses)) cs)
    in
    ( edges /= [], Graph.fromNodesAndEdges final_nodes edges )



--===========================
--== BY ENTRIES RESOLUTION ==
--===========================


openedUpdationSCFByEntriesResolutionAux : List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem )
openedUpdationSCFByEntriesResolutionAux xs new_opens =
    let
        res =
            List.foldl
                (\( li, ri ) ( ac, rest ) ->
                    let
                        add_ac =
                            LE.takeWhile (\( _, x ) -> List.length x.c <= List.length ri.c) rest
                    in
                    if List.any (\( _, x ) -> PL_NFC.cplSubsumes x.c ri.c) (ac ++ add_ac) then
                        ( ac ++ add_ac, List.drop (List.length add_ac) rest )

                    else
                        ( ac ++ add_ac ++ [ ( li, ri ) ]
                        , List.drop (List.length add_ac) rest
                        )
                )
                ( [], xs )
                new_opens
    in
    Tuple.first res ++ Tuple.second res


resolventsWithClosedSCFByEntriesResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> Int -> ResolutionItem -> List ResolutionItem
resolventsWithClosedSCFByEntriesResolutionAux closed resDone id rid =
    List.sortBy (\x -> List.length x.c) <|
        List.foldl
            (\( i, ri ) ac ->
                if (List.member id <| Maybe.withDefault [] <| Dict.get i resDone) || not (rid.p1 == 0 || ri.p1 == 0) then
                    ac

                else
                    let
                        resolvents_i =
                            List.filter (\( cj, _, _ ) -> not <| PL_NFC.cplIsTautology cj) <| cplAllResolvents rid.c ri.c
                    in
                    List.foldl
                        (\( cj, l1, l2 ) ac2 ->
                            if not <| (List.any (\x -> PL_NFC.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_NFC.cplSubsumes x.c cj) closed) then
                                List.filter (\x -> not <| PL_NFC.cplSubsumes cj x.c) ac2 ++ [ { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } ]

                            else
                                ac2
                        )
                        ac
                        resolvents_i
            )
            []
            closed


resolventsWithOpenedSCFByEntriesResolutionAux : List ( Int, ResolutionItem ) -> Int -> ResolutionItem -> List ResolutionItem
resolventsWithOpenedSCFByEntriesResolutionAux opened id rid =
    List.sortBy (\x -> List.length x.c) <|
        List.foldl
            (\( i, ri ) ac ->
                if rid.p1 /= 0 && ri.p1 /= 0 then
                    ac

                else
                    let
                        resolvents_i =
                            List.filter (\( cj, _, _ ) -> not <| PL_NFC.cplIsTautology cj) <| cplAllResolvents rid.c ri.c
                    in
                    List.foldl
                        (\( cj, l1, l2 ) ac2 ->
                            if not <| List.any (\x -> PL_NFC.cplSubsumes x.c cj) ac then
                                List.filter (\x -> not <| PL_NFC.cplSubsumes cj x.c) ac2 ++ [ { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } ]

                            else
                                ac2
                        )
                        ac
                        resolvents_i
            )
            []
            opened


csplSCFByEntriesResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> List ( Int, ResolutionItem ) -> Int -> ( List (Node ClausePL), List (Edge Literal) )
csplSCFByEntriesResolutionAux closed resDone opened nid =
    case opened of
        [] ->
            ( [], [] )

        ( id, rid ) :: xs ->
            if List.isEmpty rid.c then
                let
                    refDict =
                        Dict.fromList <| closed ++ opened
                in
                recoverResolutionPathAux id refDict

            else
                let
                    resolvents_i =
                        List.indexedMap (\i x -> ( nid + i + 1, x )) <|
                            filterSubsumedResolutionItems <|
                                List.sortBy (\x -> List.length x.c) <|
                                    resolventsWithClosedSCFByEntriesResolutionAux closed resDone id rid
                                        ++ (List.filter (\ri -> not <| List.any (\( _, x ) -> PL_NFC.cplSubsumes x.c ri.c) closed) <| resolventsWithOpenedSCFByEntriesResolutionAux xs id rid)
                in
                let
                    new_closed =
                        closed ++ [ ( id, rid ) ]

                    newResDone =
                        Dict.insert id (List.map Tuple.first (closed ++ xs)) <| Dict.map (\_ v -> v ++ [ id ]) resDone

                    new_opened =
                        openedUpdationSCFByEntriesResolutionAux xs resolvents_i
                in
                csplSCFByEntriesResolutionAux new_closed newResDone new_opened (nid + List.length resolvents_i + 1)


{-| It uses resolution by entries algorithm using shortest clause first heuristic for determining the feasibilibity of a set of clauses. It gives the insatisfactibility (True:Insat, False:SAT) and a graph with the resolution path to inconsitence. If clause set is feasible then a graph with only initial nodes is returned.

    res_SCFByEntriesResolution = csplSCFByEntriesResolution cs

    Tuple.first res_SCFByEntriesResolution == False

    res_SCFByEntriesResolution |> Tuple.second |> resolutionTableauToDOT
        == "digraph G {\\n rankdir=TB\\n graph []\\n node [shape=box, color=black]\\n edge [dir=none, color=blue, fontcolor=blue]\\n\\n\\n\\n 1 [label="{¬ p, ¬ q, r}"]\\n 2 [label="{q, p}"]\\n 3 [label="{¬ r, p}"]\\n 4 [label="{¬ p, q}"]\\n 5 [label="{¬ q, p}"]\\n 6 [label="{¬ p, ¬ r}"]\\n\\n {rank=same; 1;2;3;4;5;6;}\\n}"

Note: You can render the graph with GraphViz Viewer and _resolutionTableauToDOT_ described at the end.

-}
csplSCFByEntriesResolution : List ClausePL -> ( Bool, Graph ( Bool, ClausePL ) Literal )
csplSCFByEntriesResolution cs =
    let
        new_cs =
            List.indexedMap (\i x -> ( i + 1, { c = x, p1 = 0, p2 = 0, l1 = Atom "", l2 = Atom "" } )) <| List.sortBy (\x -> List.length x) <| PL_NFC.csplRemoveSubsumedClauses <| PL_NFC.csplRemoveTautClauses <| cs
    in
    let
        ( nodes, edges ) =
            csplSCFByEntriesResolutionAux [] Dict.empty new_cs (List.length new_cs + 1)
    in
    -- ( nodes, edges )
    let
        nid_max =
            Maybe.withDefault 0 <| List.maximum <| List.map (\x -> x.id) <| nodes

        nodes_clauses =
            List.map (\x -> x.label) <| nodes
    in
    let
        final_nodes =
            List.map (\x -> Node x.id ( List.member x.label cs, x.label )) nodes
                ++ (List.indexedMap (\i x -> Node (nid_max + i + 1) ( True, x )) <| List.filter (\x -> not (List.member x nodes_clauses)) cs)
    in
    ( edges /= [], Graph.fromNodesAndEdges final_nodes edges )



----------------------------
--==============--
-- REPRESENTATON
--==============--


{-| Express a Resolution Tableau as a string.
-}
resolutionTableauToString : ResolutionTableau -> String
resolutionTableauToString g =
    let
        toStringNode =
            \( _, cs ) -> Just <| PL_NFC.cplToString cs

        toStringEdge =
            \l -> Just (PL_SS.fplToString l)
    in
    Graph.toString toStringNode toStringEdge g


{-| Express a Resolution Tableau as a string in DOT format that is viewable with a GraphViz Render.

**Note:** If you are using elm repl, before introducing the code you must replace _\\n_ by _\\n_ and _\\"_ by _"_ in a simple text editor.

-}
resolutionTableauToDOT : ResolutionTableau -> String
resolutionTableauToDOT g =
    let
        myStyles =
            { defaultStyles | node = "shape=box, color=black", edge = "dir=none, color=blue, fontcolor=blue" }

        toStringNode =
            \( _, cs ) -> Just <| PL_NFC.cplToString cs

        toStringEdge =
            \l -> Just (PL_SS.fplToString l)

        initialNodes =
            String.join ";" <|
                List.map String.fromInt <|
                    List.foldl
                        (\x ac ->
                            if Tuple.first x.label then
                                ac ++ [ x.id ]

                            else
                                ac
                        )
                        []
                        (Graph.nodes g)
    in
    String.replace "\n}" ("\n\n  {rank=same; " ++ initialNodes ++ ";}\n}") <| Graph.DOT.outputWithStyles myStyles toStringNode toStringEdge g
