
axiom df-ldual
  let vv: setvar v
  let vf: setvar f
  let vk: setvar k
  assert |- LDual = ( v e. _V |-> ( { <. ( Base ` ndx ) , ( LFnl ` v ) >. , <. ( +g ` ndx ) , ( oF ( +g ` ( Scalar ` v ) ) |` ( ( LFnl ` v ) X. ( LFnl ` v ) ) ) >. , <. ( Scalar ` ndx ) , ( oppR ` ( Scalar ` v ) ) >. } u. { <. ( .s ` ndx ) , ( k e. ( Base ` ( Scalar ` v ) ) , f e. ( LFnl ` v ) |-> ( f oF ( .r ` ( Scalar ` v ) ) ( ( Base ` v ) X. { k } ) ) ) >. } ) )
end
