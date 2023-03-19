
axiom df-voln
  let vx: setvar x
  assert |- voln = ( x e. Fin |-> ( ( voln* ` x ) |` ( CaraGen ` ( voln* ` x ) ) ) )
end
