
axiom df-ldlf
  let vx: setvar x
  assert |- Ldlf = CovHasRef { x | x ~<_ _om }
end
