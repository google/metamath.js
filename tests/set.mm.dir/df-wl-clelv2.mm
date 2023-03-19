
axiom df-wl-clelv2
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  assert |- ( x wl-el2 A <-> A. u ( u = x -> u wl-el A ) )
end
