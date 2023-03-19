
axiom df-phtpc
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  assert |- ~=ph = ( x e. Top |-> { <. f , g >. | ( { f , g } C_ ( II Cn x ) /\ ( f ( PHtpy ` x ) g ) =/= (/) ) } )
end
