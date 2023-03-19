include "c0.mm"
include "wne.mm"
include "cin.mm"
include "ciin.mm"
include "iinin2.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "incom.mm"
include "a1i.mm"
include "iineq2i.mm"
include "3eqtr4g.mm"

theorem iinin1
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
  assert |- ( A =/= (/) -> |^|_ x e. A ( C i^i B ) = ( |^|_ x e. A C i^i B ) )

  proof
    cA
    c0
    wne
    vx
    cA
    cB
    cC
    cin
    #
    ciin
    cB
    vx
    cA
    cC
    ciin
    #
    cin
    vx
    cA
    cC
    cB
    cin
    #
    ciin
    @1
    cB
    cin
    vx
    cA
    cB
    cC
    iinin2
    vx
    cA
    @2
    @0
    @2
    @0
    wceq
    vx
    cv
    cA
    wcel
    cC
    cB
    incom
    a1i
    iineq2i
    @1
    cB
    incom
    3eqtr4g
end
