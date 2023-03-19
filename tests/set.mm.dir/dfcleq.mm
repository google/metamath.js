include "axext3.mm"
include "df-cleq.mm"

theorem dfcleq
  param vx: setvar x
  param cA: class A
  param cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( A = B <-> A. x ( x e. A <-> x e. B ) )

  proof
    vx
    vy
    vz
    cA
    cB
    vy
    vz
    vx
    axext3
    df-cleq
end
