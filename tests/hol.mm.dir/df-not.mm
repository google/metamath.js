
axiom df-not
  let vp: var p
  assert |- T. |= [ ~ = \ p : bool . [ p : bool ==> F. ] ]
end
