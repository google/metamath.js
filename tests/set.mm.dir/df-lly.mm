
axiom df-lly
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let vj: setvar j
  assert |- Locally A = { j e. Top | A. x e. j A. y e. x E. u e. ( j i^i ~P x ) ( y e. u /\ ( j |`t u ) e. A ) }
end
