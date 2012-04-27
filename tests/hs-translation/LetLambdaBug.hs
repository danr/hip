module LetLambdaBug where

const x = \y -> let res = x in res

