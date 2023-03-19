
axiom df-ditg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assert |- S_ [ A -> B ] C _d x = if ( A <_ B , S. ( A (,) B ) C _d x , -u S. ( B (,) A ) C _d x )
end
