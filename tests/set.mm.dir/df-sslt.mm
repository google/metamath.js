
axiom df-sslt
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  assert |- <<s = { <. a , b >. | ( a C_ No /\ b C_ No /\ A. x e. a A. y e. b x <s y ) }
end
