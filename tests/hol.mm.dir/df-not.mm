
axiom df-not
  param vp: var p
  assert |- T. |= [ ~ = \ p : bool . [ p : bool ==> F. ] ]
end
