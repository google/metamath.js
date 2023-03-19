include "ax-cnre.mm"

theorem cnre
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( A e. CC -> E. x e. RR E. y e. RR A = ( x + ( _i x. y ) ) )

  proof
    vx
    vy
    cA
    ax-cnre
end
