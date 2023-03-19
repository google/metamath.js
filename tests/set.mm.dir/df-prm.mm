
axiom df-prm
  let vn: setvar n
  let vp: setvar p
  assert |- Prime = { p e. NN | { n e. NN | n || p } ~~ 2o }
end
