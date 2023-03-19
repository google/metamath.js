include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "cab.mm"
include "ciin.mm"
include "raleq.mm"
include "abbidv.mm"
include "df-iin.mm"
include "3eqtr4g.mm"

theorem iineq1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( A = B -> |^|_ x e. A C = |^|_ x e. B C )

  proof
    cA
    cB
    wceq
    #
    vy
    cv
    cC
    wcel
    #
    vx
    cA
    wral
    #
    vy
    cab
    @1
    vx
    cB
    wral
    #
    vy
    cab
    vx
    cA
    cC
    ciin
    vx
    cB
    cC
    ciin
    @0
    @2
    @3
    vy
    @1
    vx
    cA
    cB
    raleq
    abbidv
    vx
    vy
    cA
    cC
    df-iin
    vx
    vy
    cB
    cC
    df-iin
    3eqtr4g
end
