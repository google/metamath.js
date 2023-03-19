include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wral.mm"
include "incom.mm"
include "eqeq1i.mm"
include "disj.mm"
include "bitri.mm"

theorem disjr
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( ( A i^i B ) = (/) <-> A. x e. B -. x e. A )

  proof
    cA
    cB
    cin
    #
    c0
    wceq
    cB
    cA
    cin
    #
    c0
    wceq
    vx
    cv
    cA
    wcel
    wn
    vx
    cB
    wral
    @0
    @1
    c0
    cA
    cB
    incom
    eqeq1i
    vx
    cB
    cA
    disj
    bitri
end
