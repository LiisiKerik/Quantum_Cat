-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Standard where
  import Tree
  data Def_tree' = Def_tree'(Decl_tree)(Type_tree)(Expression_tree') deriving(Show)
  data Expression_branch' =
    Expression_application'(Expression_tree')(Expression_tree') |
    Expression_function'(String, Type_tree)(Expression_tree', Type_tree) |
    Expression_int'(Integer) |
    Expression_match'(Expression_tree')([Match_tree']) |
    Expression_name'(String)([Type_tree])([Int_tree])
      deriving(Show)
  data Expression_tree' = Expression_tree'(Integer)(Integer)(Expression_branch') deriving(Show)
  data Match_tree' = Match_tree'(Name_tree)([Name_tree])(Expression_tree') deriving(Show)
  data Tree' = Tree'([Data_tree])([Def_tree']) deriving(Show)
  standard :: Tree -> Tree'
  standard(Tree(x)(y)) = Tree'(x)(standard_def <$> y)
  standard_arguments :: [Argument_tree] -> Type_tree -> Expression_tree' -> (Type_tree, Expression_tree')
  standard_arguments([])(x)(y) = (x, y)
  standard_arguments(Argument_tree(l1)(c1)(x)(y @ (Type_tree(l2)(c2)(_))) : z)(w)(a) =
    (Type_tree(l2)(c2)(Function_type(y)(b)), Expression_tree'(l1)(c1)(Expression_function'(x, y)(c, b))) where
      (b, c) = standard_arguments(z)(w)(a)
  standard_def :: Def_tree -> Def_tree'
  standard_def(Def_tree(d)(w)(a)(b)) = uncurry(Def_tree'(d))(standard_arguments(w)(a)(standard_expr(b)))
  standard_expr :: Expression_tree -> Expression_tree'
  standard_expr(Expression_tree(l)(c)(e)) = let
    st_exp(Expression_tree'(_)(_)(e'))([]) = e'
    st_exp(e1)(e2 : es) = st_exp(Expression_tree'(l)(c)(Expression_application'(e1)(e2)))(es) in
      Expression_tree'(l)(c)(case e of
        Expression_application(e')(es) -> st_exp(standard_expr(e'))(standard_expr <$> es)
        Expression_int(x) -> Expression_int'(x)
        Expression_match(e')(m) -> Expression_match'(standard_expr(e'))(standard_match <$> m)
        Expression_name(x)(t)(n) -> Expression_name'(x)(t)(n))
  standard_match :: Match_tree -> Match_tree'
  standard_match(Match_tree(x)(y)(z)) = Match_tree'(x)(y)(standard_expr(z))
  standard_tree :: Tree -> Tree'
  standard_tree(Tree(x)(y)) = Tree'(x)(standard_def <$> y)
-----------------------------------------------------------------------------------------------------------------------------