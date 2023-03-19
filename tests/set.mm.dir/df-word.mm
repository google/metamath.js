
axiom df-word
  let vw: setvar w
  let cS: class S
  let vl: setvar l
  assert |- Word S = { w | E. l e. NN0 w : ( 0 ..^ l ) --> S }
end
