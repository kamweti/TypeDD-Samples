-- This Idris code defines a binary tree data structure and implements a few operation on it:
--      * equality
--      * mapping
--      * folding
-- A binary tree is a recursive data type.
-- The Tree type is parameterized by a type elemType which represents the type of values stored in the tree
-- A tree can be either
--     * Empty (representin an empty tree)
--     * Node that contains a value of type elemType and two subtrees that are also of type Tree elemType
--         * left
--         * right
-- Equality
--  * The Eq interface is implemented for Tree.
--  * This allows trees to be compared for equality
--  * Two trees are equal if they are both empty or if they are both Nodes with equal left and right subtrees and equal elements
-- Mapping
--  * The Functor interface is implemented for Tree, allowing a function to be applied uniformly across the tree
--  * The `map` function applies the function to the element at each node and recursively applies it to the left and right subtrees
-- Folding
--  * The foldable interface is implemented for Tree allowing a binary operation


data Tree elemType = Empty
               | Node (Tree elemType) elemType (Tree elemType)

Eq elemType => Eq (Tree elemType) where
    (==) Empty Empty = True
    (==) (Node left root right) (Node left' root' right')
          = left == left' && root == root' && right == right'
    (==) _ _ = False

Functor Tree where
    map func Empty = Empty
    map func (Node left root right)
        = Node (map func left)         -- Applies func uniformly across the left subtree
               (func root)             -- Applies func to the element at the node
               (map func right)        -- Applies func uniformly cross the right subtree

Foldable Tree where
  foldr f acc Empty = acc
  foldr f acc (Node left e right) = let leftfold = foldr f acc left
                                        rightfold = foldr f leftfold right in
                                        f e rightfold
