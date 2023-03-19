
axiom df-t0
  let vx: setvar x
  let vy: setvar y
  let vj: setvar j
  let vo: setvar o
  assert |- Kol2 = { j e. Top | A. x e. U. j A. y e. U. j ( A. o e. j ( x e. o <-> y e. o ) -> x = y ) }
end
