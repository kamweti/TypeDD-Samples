data Tree val = Empty
               | Node (Tree val) val (Tree val)

Eq val => Eq (Tree val) where
    (==) Empty Empty = True
    (==) (Node left e right) (Node left' e' right')
          = left == left' && e == e' && right == right'
    (==) _ _ = False

Functor Tree where
    map f Empty = Empty
    map f (Node left e right)
        = Node (map f left)         -- Applies func uniformly across the left subtree
               (f e)                -- Applies func to the element at the node
               (map f right)        -- Applies func uniformly cross the right subtree

Foldable Tree where
  foldr f acc Empty = acc
  foldr f acc (Node left e right) = let leftfold = foldr f acc left
                                        rightfold = foldr f leftfold right in
                                        f e rightfold
