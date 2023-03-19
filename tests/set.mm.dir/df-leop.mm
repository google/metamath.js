
axiom df-leop
  let vx: setvar x
  let vu: setvar u
  let vt: setvar t
  assert |- <_op = { <. t , u >. | ( ( u -op t ) e. HrmOp /\ A. x e. ~H 0 <_ ( ( ( u -op t ) ` x ) .ih x ) ) }
end
