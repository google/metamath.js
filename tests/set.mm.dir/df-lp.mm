
axiom df-lp
  let vx: setvar x
  let vy: setvar y
  let vj: setvar j
  assert |- limPt = ( j e. Top |-> ( x e. ~P U. j |-> { y | y e. ( ( cls ` j ) ` ( x \ { y } ) ) } ) )
end
