
axiom df-haus
  let vx: setvar x
  let vy: setvar y
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  assert |- Haus = { j e. Top | A. x e. U. j A. y e. U. j ( x =/= y -> E. n e. j E. m e. j ( x e. n /\ y e. m /\ ( n i^i m ) = (/) ) ) }
end
