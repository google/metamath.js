include "ax-cnre.mm"

theorem cnre
  param vx: setvar x
  param vy: setvar y
  param cA: class A

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
