
axiom df-cndprob
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  assert |- cprob = ( p e. Prob |-> ( a e. dom p , b e. dom p |-> ( ( p ` ( a i^i b ) ) / ( p ` b ) ) ) )
end
