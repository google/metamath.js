
axiom ax-wl-8cl
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assert |- ( x = y -> ( x wl-el A -> y wl-el A ) )
end
