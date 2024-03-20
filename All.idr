module Main

import Data.String
import Data.Vect
import System
import System.REPL
import Decidable.Equality
import Data.Vect.Elem

namespace Chapter1
    {-
        * Compiling and Running an Idris program
     -}
    export
    main : IO ()
    main = putStrLn "Hello, Idris World"

namespace Chapter2

    {-
        - A complete Idris program to calculate average word length
        - `_string` is a String containing words separated by a whitespace e.g "hermes arrived at home"
        - `words` function is imported from Data.String
        - run using
            ```
            idris2 All.idr
            :exec Chapter2.runAverage
            ```
    -}

    average : (str : String) -> Double
    average str = let totalWords = countWords str
                      stringLength = sumLengths (words str) in
                      (cast stringLength / cast totalWords)
                where
                    countWords : String -> Nat
                    countWords str = length (words str)
                    sumLengths : List String -> Nat
                    sumLengths [] = 0
                    sumLengths (x :: xs) = (length x) + (sumLengths xs)

    showAverage : String -> String
    showAverage str = "The average word length is : " ++ show (average str) ++ "\n"

    export
    runAverage : IO()
    runAverage = repl "Enter a String " showAverage

    {-
        * Tuples and pairs

        - internally, all turples other tna the empty tuple are stored as nested pairs
        - if you write (1, 2, 3, 4), Idris will treat it the same way as (1, (2, (3, 4)))
            ```
                Main> :t (1, 2, 3, 4)
                (1, (2, (3, 4))) : (Integer, (Integer, (Integer, Integer)))
            ```
    -}

    {-
        * Type of map

        - if you check the type of `map` at the REPL, you see something slightly different
        ```
        Main> :t map
        Prelude.map : Functor f => (a -> b) -> f a -> f b
        ```
        - the reason for this is that map can work on a variety of types not just lists
        - therefore it has a constrained generic type

        - the `filter` function is another higher-order function that filters a list according to a Boolean function
            ```
            Main> :t filter
            Prelude.List.filter : (a -> Bool) -> List a -> List a
            ```
        - it returns a new list of everything in the input list for which the function returns True
        - example
            ```
            Main> filter (>10) [1, 12, 34, 5, 67]
            [12, 34, 67]
            ```
    -}

    {-
        * Overloading functions

        - `length` function in the average example above works for both lists and strings
        - this is because Idris allows function names to be overloaded to work on multiple types
            ```
            Main> :t length
            Data.List1.length : List1 a -> Nat
            Prelude.List.length : List a -> Nat
            Prelude.SnocList.length : SnocList a -> Nat
            Prelude.String.length : String -> Nat
            ```
        - length is defined in multiple namespaces and Idris decides which length function to use based on the context
    -}


    {-
        * Calculating the average word length in a string using overloading functions map, sum
     -}
    export
    updatedAverage : (str : String) -> Double
    updatedAverage str = let totalWords = countWords str
                             totalChars = sum (sumLengths (words str))
                        in
                            cast totalChars / cast totalWords
                        where

                            countWords : String -> Nat
                            countWords str = length (words str)

                            sumLengths : List String -> List Nat
                            sumLengths strs =  map length strs
    {-
        * Modules and namespaces
        https://idris2.readthedocs.io/en/latest/tutorial/modules.html

        - An Idris program consists of a collection of modules
        - Each module includes an **optional** module declaration giving :
            - the name of the module
            - a list of import statements of other modules
            - a collection of declarations and definitions of types
            - interfaces
            - functions
        - Example:
            ```
            module Main
            import BTree

            main : IO ()
            ```

        - There is no formal link between a module name and its file name although it is generally advisable to use the same name for each
        - An import statement refers to a filename, using dots to separate directories
        - For example, import foo.bar would import the file Foo/Bar.idr
        - bar.idr would conventionally have the module declaration
            ```
            module Foo.Bar
            ```
        - the only requirement for module names is that the main module with the main function must be called Main
            ```
            module Main

            main : IO()
            ```
        - the file name for this module need not be `Main.idr`

        * Export Modifiers

        - Idris allows for fine-grained control over the visibility of a namespace's contents
        - By default, all names defined in a namescpace are kepy private so as to have a minimal interface and internal details to be hidden
        - Idris allows for functions, types and interfaces to be marked as
            - private (default) - means that it is not exported at all
            - export            - means that its top level type is exported
            - public export     - means thtat the entire definition is exported

        TODO: come back to this section
    -}

    {-
        * Whitespace significance: the layout rule

        TODO: come back to this section
    -}

    {-
        * Documentation Comments

        TODO: come back to this section
    -}

    {-
        * Interactive programs

        - the entry point to a compiled Idris program is `main` defined in a `Main` module
        - Main.main must have the type `IO ()`, it returns an IO action that produces an empty tuple

        TODO: come back to this section later
    -}

namespace Chapter3

    {-
        * Calculating word lengths by pattern matching on the list (WordLength.idr)
    -}
    export
    allLengths : List String -> List Nat
    allLengths [] = []
    allLengths (x :: xs) = length x :: allLengths xs

    {-
        * Vectors: lists with lengths encoded in the type

        - you have to import Data.Vect lib
     -}

    export
    fourInts : Vect 4 Int
    fourInts = [0, 2, 3, 4]

    {-
        * Refining allLengths to use Vect instead

        - this provides a gurantee that the length of the input must be equal to the lenght of the output
     -}

    export
    allLengthsRefined : Vect len String -> Vect len Nat
    allLengthsRefined [] = []
    allLengthsRefined (x :: xs) = length x :: allLengthsRefined xs

namespace Chapter4

    {-
        * Enumerated data types
     -}
    data Direction = East | West | North | South

    {-
        * Union data types

        - an extension of an enumerated type
        - the constructors of the type can themselves carry data
        - Example: the sides of various shapes
        ```
            data Shape = Triangle Double Double Double
            | Rectangle Double Double Double Double
            | Circle Double
        ```
     -}

    {-
        * Recursive types

        - a union data type where the type constructors carry data of the type itself
        - example:
            ```
            data Nat = Z | S Nat
            ```
     -}

    {-
        * The %name directive

        TODO: Come back to this section
     -}


    {-
        * Defining binary trees

        - Binary trees are commonly used to store ordered information
        - where everything in a node's left subtree is smaller than the value at the node
        - and everything in the right subtree is larger than the value at the node
        - such trees are called binary search trees
     -}

    data Tree elemType = Empty
                    | Node (Tree elemType) elemType (Tree elemType)

    {-
        * Insert a value into a binary search tree
     -}
    export
    insert : Ord elemType => elemType -> Tree elemType -> Tree elemType
    insert x Empty = Node Empty x Empty
    insert x (Node left value right) = case compare x value of
                                        LT => Node (insert x left) value right
                                        EQ => Node left value right
                                        GT => Node left value (insert x right)

    {-
        * @ patterns

        - TODO: come back to this section later
     -}

    {-
        * Defining dependent data types

        - a dependent data type is a type that is computed from some other value
        - Vect is an example that we've already seen
            ```
            Vect : Nat -> Type -> Type
            ```
    -}

    {-
        * Defining a dependent type for vehicles with their power source in the type
     -}
    data PowerSource = Petrol | Pedal
    data Vehicle : PowerSource -> Type where
        Bicycle : Vehicle Pedal
        Car : (fuel : Nat) -> Vehicle Petrol
        Bus : (fuel : Nat) -> Vehicle Petrol

    {-
        - we can write funcitons that will work on all vehicles (by using a type argument) or constrain to some (by explicitly stating the type)
     -}
    wheels : Vehicle powersource -> Nat
    wheels Bicycle = 2
    wheels (Car fuel) = 4
    wheels (Bus fuel) = 28

    engineCC : Vehicle Petrol -> Nat
    engineCC (Car fuel)  = 1800
    engineCC (Bus fuel)  = 3000

    {-
        * Type level expressions

        - The expression n + m in the return type here is an ordinary expression with type Nat
     -}
    export
    append : Vect len1 elemType -> Vect len2 elemType -> Vect (len1 + len2) elemType
    append [] ys = ys
    append (x :: xs) ys = x :: append xs ys

    {-
        * Parameters and Indicies

        - `Vect len elemType` Vect is a family of types that are indexed by length and parameterized by an element type
            - parameter is unchanged across the entire structure
            - an index may change across a structure
        - the disctintion is useful when looking at a function's type, you can be certain that the specific value of a parameter can play no part in a function's definition
     -}

    {-
        * Indexing vectors with bounded numbers using `Fin`

        - because Vect carry's length as part of the type, the type checker has additional knowledge that can be used
            if we wish to look up an element in a Vect
        - length also ensures that the locaiton cannot be out of bounds when the program is ran
        - the `index` function defined in `Data.Vect` is a bounds-safe lookup funciton whose type guarantees that it will never access a location that is outside the bounds of a vector
            ```
            Main> :t index
            Data.Vect.index : Fin len -> Vect len elem -> elem
            ```
        - the name Fin suggests that the number is finitely bounded
        - example, when looking up an element by location, you can use a number within the bounds of the vector
            ```
            Main> :import Data.Vect
            Imported module Data.Vect
            Main> :let fourInts : Vect 4 Int
            Main> fourInts = [2, 3, 4, 5]
            Main> index 1 fourInts
            index (FS FZ) fourInts

            ```
     -}

    {-
        * The `Nat` type

        - represents unbounded unsigned integers
        - in Idris a natural number is defined as being either zero or the successor of another natural number
            ```
            Main> :doc Nat
            data Prelude.Nat : Type
            Natural numbers: unbounded, unsigned integers which can be pattern matched.
            Totality: total
            Visibility: public export
            Constructors:
                Z : Nat
                Zero.
                S : Nat -> Nat
                Successor.
            ```
        - since data types are defined in terms of their constructors, in the case of `Nat`, every value of type `Nat` must either be
            zero or the successor of another Nat
            ```
            Main> :let three = 3
            Main> :let three_alt = (S (S (S Z)))
            Main> three_alt
            3
            ```
     -}

     {-
        * `Fin` type is provided by the compiler to guarantee that the value is within the bounds stated in the type

        ```
        data Data.Fin.Fin : Nat -> Type
        Numbers strictly less than some bound.  The name comes from "finite sets".

        It's probably not a good idea to use `Fin` for arithmetic, and they will be
        exceedingly inefficient at run time.
        @ n the upper bound
        Totality: total
        Visibility: public export
        Constructors:
            FZ : Fin (S k)
            FS : Fin k -> Fin (S k)
        ```
    -}

    {-
    * Complete implementation of a simple data store
    -}
    export
    data DataStore : Type where
        MkData : (size : Nat) -> (items : Vect size String) -> DataStore

    size : DataStore -> Nat
    size (MkData size' items') = size'

    items : (store : DataStore) -> Vect (size store) String
    items (MkData size' items') = items'

    addToStore : DataStore -> String -> DataStore
    addToStore (MkData size store) newitem = MkData _ (addToData store)
    where
        addToData : Vect oldsize String -> Vect (S oldsize) String
        addToData [] = [newitem]
        addToData (x :: xs) = x :: addToData xs

    data Command = Add String
                | Get Integer
                | Quit

    parseCommand : String -> String -> Maybe Command
    parseCommand "add" str = Just (Add str)
    parseCommand "get" val = case all isDigit (unpack val) of
                                False => Nothing
                                True => Just (Get (cast val))
    parseCommand "quit" "" = Just Quit
    parseCommand _ _ = Nothing

    parse : (input : String) -> Maybe Command
    parse input = case span (/= ' ') input of
                    (cmd, args) => parseCommand cmd (ltrim args)

    getEntry : (pos : Integer) -> (store : DataStore) ->
            Maybe (String, DataStore)
    getEntry pos store
        = let store_items = items store in
            case integerToFin pos (size store) of
                Nothing => Just ("Out of range\n", store)
                Just id => Just (index id store_items ++ "\n", store)

    processInput : DataStore -> String -> Maybe (String, DataStore)
    processInput store input
        = case parse input of
            Nothing => Just ("Invalid command\n", store)
            Just (Add item) =>
                Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
            Just (Get pos) => getEntry pos store
            Just Quit => Nothing

    storeMain : IO ()
    storeMain = replWith (MkData _ []) "Command: " processInput

namespace Chapter5
    {-
        * IO () type

        - describes sequences of interactions
        - the Idris runtime runs those actions
        - example
     -}

    do_some_actions : IO ()
    do_some_actions = do
        putStr "Enter your name"
        x <- getLine
        putStrLn ("hello " ++ x ++ "!")

    {-
        * IO action sequencing using the do notation

        - this is the recommended way of sequencing
           ```
           do result_of_execution <- execute_action
           ```
        - `let` can also be used inside do blocks to assign a pure expression to a variable
            ```
            printLength : IO ()
            printLength = do putStr "Input string: "
                             input <- getLine
                             let len = length input
                             putStrLn (show len)
            ```
        - `let` and `<-` in do blocks
            - `let x = expression` is used to assign the result of the evaluation of an expression
            - `<-` is used to assign the result of the exectuion of action to a variable
    -}

    {-
        * The `pure` function is used to produce a value in an interactive program without having any other input/output effects when it is executed

        - it is useful to "lift" values into a context
        - especially useful while working with data structures that can contain values like Maybe, List

        ```
            Main> :let example : Maybe Nat
            Main> example = pure 45
            example = Just 45
        ```
        - in this exmaple, `pure 45` takes the integer `45` and wraps it into a `Maybe` context resulting in `Just 45`

        - another example below
        ```
        Main> :exec Main.Chapter4.pureExample
        The value is 10
        ```
     -}
    export
    pureExample : IO ()
    pureExample = do
        val <- pure 10
        putStrLn $ "The value is " ++ show val

    {-
        * Pattern matching on the the execution result
     -}
    export
    pureExample2 : IO ()
    pureExample2 = do
        val <- pure (Just 10)
        case val of
            Nothing => putStrLn $ "Nothing"
            Just x => putStrLn $ "The value is " ++ show val

    {-
        * Recursively call an Interactive program

        ```
        Main> :exec Main.Chapter4.countdownTimer 32
        ```
     -}
    export
    countdownTimer : (secs : Nat) -> IO ()
    countdownTimer Z = putStrLn "Lift off!"
    countdownTimer (S secs) = do
            putStrLn (show (S secs))
            usleep 1000000
            countdownTimer secs

    {-
        * Reading a Vect of known length from the console
        ```
        Main> :exec Main.Chapter4.readVectOfLen 3 >>= printLn
        james
        maddy
        tom
        ["james", "maddy", "tom"]
        ```
     -}
    export
    readVectOfLen : (len : Nat) -> IO (Vect len String)
    readVectOfLen 0 = pure []
    readVectOfLen (S k) = do
            x <- getLine
            xs <- readVectOfLen k
            pure (x :: xs)

    {-
        * Reading a Vect of uknown lenth from console
     -}
    data VectUnknown : Type -> Type where
        MakeVect : (len : Nat) -> Vect len a -> VectUnknown a

    export
    readVectUnknown : IO (VectUnknown String)
    readVectUnknown = do
            x <- getLine
            if (x == "")
                then pure (MakeVect _ [])
                else do MakeVect _ xs <- readVectUnknown
                        pure (MakeVect _ (x :: xs))
    {-
        - running the function yields
        ```
        Main> :exec Main.Chapter4.readVectUnknown >>= printLn
        Error: Can't find an implementation for Show (VectUnknown String).
        ```
        - we need to define a convenience function that displays the contents of VectUnknown to the console

        ```
            Main> :exec readVectUnknown >>= printVectUnknown
            "kamweti"
            "muriuki"
            "is"
            "a"
            "genius"

            ["\"kamweti\"", "\"muriuki\"", "\"is\"", "\"a\"", "\"genius\""] (length 5)
        ```
     -}
    export
    printVectUnknown : Show a => VectUnknown a -> IO ()
    printVectUnknown (MakeVect len xs) = putStrLn (show xs ++ " (length " ++ show len ++ ")")

    {-
        * Dependent pairs are a more expressive form of Tuple construct where the type of the second element in the pair
        is computed from the value of the first element

        - dependent pairs are writtend with the elements separated by `**`

        ```
        Main>  :let anyVect : (n : Nat ** Vect n String)
        Main> anyVect = (3 ** ["just", "do", "it"])
        anyVect = (3 ** ["just", "do", "it"])
        ```

        - you can ommit the type of the first element and Idris will infer it for your
        - this is also valid
        ```
        Main>  :let anyVect : (n ** Vect n String)
        ```
     -}

    {-
        * we can rewrite readVectUknown to return a dependent pair
        * with the added benefit that `printLn` can display contents of a dependent pair

        ```
        Main> :exec readVectUnknownDependentPair >>= printLn
        "jamie"
        "get"
        "some"
        "garlic"

        (4 ** ["\"jamie\"", "\"get\"", "\"some\"", "\"garlic\""])
        ```
     -}
    export
    readVectUnknownDependentPair : IO (len ** Vect len String)
    readVectUnknownDependentPair = do
        x <- getLine
        if (x == "")
            then pure (_ ** [])
            else do (_ ** xs) <- readVectUnknownDependentPair
                    pure (_ ** (x :: xs))

    {-
        * Validating the inputs vectors are of the same length using
            - dependent pairs
            - and `exactLength` in `Data.Vect`

        - an example of zipInputs
        ```
        Main> :exec zipInputs
        Enter first vector (with a blank line to end)
        "jamie"
        "please"
        "rush"

        Enter the second vector (with a blank line to end)
        "to"
        "the"
        "market"

        [("\"jamie\"", "\"to\""), ("\"please\"", "\"the\""), ("\"rush\"", "\"market\"")]
        ```
     -}
    export
    zipInputs : IO ()
    zipInputs = do
        putStrLn "Enter first vector (with a blank line to end)"
        (first_len ** first_vect) <- readVectUnknownDependentPair
        putStrLn "Enter the second vector (with a blank line to end)"
        (second_len ** second_vect) <- readVectUnknownDependentPair
        case exactLength first_len second_vect of
            Nothing => putStrLn "Vectors are of different lengths"
            Just second_vect' => printLn (zip first_vect second_vect')

namespace Chapter6

    {-
        * Computing types using type synonyms to give informative names to complex types
     -}
    pointsInASquare : Vect 4 (Double, Double)
    pointsInASquare = [
        (0.0, 0.0),
        (0.0, 0.0),
        (0.0, 0.0),
        (0.0, 0.0)
    ]

    {-
        * we can go further and define a type synonym for a point in a square

        - we define a function PositionXY that takes no arguments and returns a Type
        - by convention, we use an initial capital letter for functions that are intended to compute types
     -}
    PositionXY : Type
    PositionXY = (Double, Double)
    pointsInASquare2 : Vect 4 PositionXY

    {-
        - functions intended to compute types can also take arguments
     -}
    PolyGon : Nat -> Type
    PolyGon n = Vect n PositionXY
    pointsInSquare3 : PolyGon 4

    {-
        - Functions with an unknown number of arguments

        - an addition function with a variable number of arguments
        - an AdderType function that will be used to compute the value of the add  function
     -}
    AdderType : (countArgs : Nat) -> Type
    AdderType 0 = Int
    AdderType (S k) = (next : Int) -> AdderType k

    export
    adder : (countArgs : Nat) -> (accum : Int) -> AdderType countArgs
    adder 0 accum = accum
    adder (S k) accum = \next => adder k (next + accum)

    {-
        * Formatted output : a type-safe printf function

        - this is another example of a function with a variable number of arguments
        - prinf produces formatted output given a format string and a variable number of arguments
        - we write a data type describing all the possible formats as follows
        - this gives a clean separation between parsing and processing of the string
        ```
            Str (Lit " = " (Number End)) would represent the format string "%s = %d"
        ```
     -}

    data Format = Number Format
                | Str Format
                | Literal String Format
                | End
    {-
        - In type-driven development process, we often thin about function in terms of transformations between data types
        - to do this, we define intermediate types such as `Format` in this section
        - we can calculate the type of printf from a Format specifier
     -}

    PrintfType : Format -> Type
    PrintfType (Number x) = (i : Int) -> PrintfType x
    PrintfType (Str x) = (str : String) -> PrintfType x
    PrintfType (Literal str x) = PrintfType x
    PrintfType End = String

    {-
        - we can now define helper function for printf, building a String from a Format
        - @todo: come back to this section later
    -}
    printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
    printfFmt (Number x) acc = ?hole_0
    printfFmt (Str x) acc = ?hole_1
    printfFmt (Literal str x) acc = ?hole_2
    printfFmt End acc = ?hole_3


namespace Chapter7
namespace Chapter8

namespace Chapter9

    {-
        * Expressing guarantees while removing an element from a Vect

        - we would expect the following of a removeElem funciton that removes a specific element from a vector
            - that the input vector is not empty
            - that the length of the output vector is one less than the input vector
    -}
    removeElem : (needle : a) -> (haystack : Vect (S n) a) -> Vect n a
    removeElem needle (x :: xs) = ?hole_4

    {-
        - Idris gives us only one pattern because xs cannot be an empty vector

        - if the value we are looking for is equal to x, we can remove it from the list by returning xs
        - we use decidable equality to be certain that the equality test is accurate
    -}

    removeElem2 : DecEq a => (needle : a) -> (haystack : Vect (S n) a) -> Vect n a
    removeElem2 needle (x :: xs) = case decEq needle x of
                                        Yes proof_ => xs
                                        No contradiction_ => ?hole
    {-
        - we might hope to resolve the hole by recursively calling removeElem2, but this renders an error

        ```
            removeElem3 : DecEq a => (needle : a) -> (haystack : Vect (S n) a) -> Vect n a
            removeElem3 needle (x :: xs) = case decEq needle x of
                                        Yes proof_ => xs
                                        No contradiction_ => x :: removeElem3 needle xs
        ```
		- the problem here is that `removeElem` requires a vector that is guaranteed to be non-empty but `xs` may be empty
			- we can see this from the type, `Vect n a` the n could stand for any natural number, including zero
			- the problem arises because there is no guarantee that value will appear in the vector, so it’s possible to reach the end of the vector without encountering it
				- if such a case happens, there is no value to remove, so you can’t satisfy the type

    -}

    {-
        * Using the Elem type to guarantee that a value is in a vector

        - we can define a type, `Elem` with a constructor that means that if we have a value of type `elemType`
            and a vector `haystack` that contains the value, we should be able to construct an element of the type `Elem value xs`
        ```
        Elem : (needle : elemType) -> (haystack : Vect len elemType) -> Type
        ```
    -}

    {-
        - we can express a contract that is a proof that an element is indeed in the vector by constructing functions of this type
        ```
        oneInVector : Elem 1 [1, 2, 3]
        ```
    -}

    {-
        - we can also be able to express a contract that is a contradiction that an element is not in the vector
        ```
        oneNotInVector : Elem 1 [2, 3, 4] -> Void
        ```
    -}

    {-
        * Using Data.Vect.Elem, we can define removeELem
    -}
    export
    removeElem3 : {len     : _}                        ->
                (needle    : elemType)                 ->
                (hayStack  : Vect (S len) elemType)    ->
                (proof_    : Elem needle hayStack)     -> Vect len elemType
    removeElem3 needle (needle :: haystack) Here                = haystack
    removeElem3 {len = 0} needle (y :: []) (There later)        = absurd later
    removeElem3 {len = (S k)} needle (y :: xs) (There later)    = y :: removeElem3 needle xs later

    {-
        - calling the method

        ```
            TypeDD-Samples (master) ✗  idris2 All.idr
            Main> :let needle : Int
            Main> needle = 3
            Main> :let haystack : Vect 5 Int
            Main> haystack = [1, 2, 3, 4, 5]
            Main> :let proofNeedleExistsInHaystack : Elem needle haystack
            Main> proofNeedleExistsInHaystack = Elem needle haystack
            Main> removeElem3 needle haystack proofNeedleExistsInHaystack
            Main> :t removeElem3 needle haystack proofNeedleExistsInHaystack
            removeElem3 needle haystack proofNeedleExistsInHaystack : Vect 4 Int
        ```
     -}

    {-
        * One caveat of removeElem3 is that you have to specify a proof everytime you call the method
        * Idris can compute proofs at runtime using the `auto` keyword
    -}
    export
    removeElemAutoProof : {len                : _}                              ->
                        (needle               : elemType)                       ->
                        (haystack             : Vect (S len) elemType)          ->
                        {auto proof_          : Elem needle haystack }          ->
                        Vect len elemType
    removeElemAutoProof needle haystack {proof_} = removeElem3 needle haystack proof_

    export
    removeElem4 : {len            : _}                              ->
                  (needle         : elemType)                       ->
                  (hayStack       : Vect (S len) elemType)          ->
                  {auto proof_    : Elem needle hayStack}           -> Vect len elemType
    removeElem4 needle (needle :: haystack) {proof_ = Here}                    = haystack
    removeElem4 {len = 0} needle (y :: []) {proof_ = There later}              = absurd later
    removeElem4 {len = (S k)} needle (y :: xs) {proof_ = There later}          = y :: removeElem4 needle xs