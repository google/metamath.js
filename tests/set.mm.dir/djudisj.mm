include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "cvv.mm"
include "wss.mm"
include "djussxp.mm"
include "incom.mm"
include "xpdisj1.mm"
include "syl5eq.mm"
include "ssdisj.mm"
include "sylancr.mm"

theorem djudisj
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D

  disjoint A x
  disjoint B y
  assert |- ( ( A i^i B ) = (/) -> ( U_ x e. A ( { x } X. C ) i^i U_ y e. B ( { y } X. D ) ) = (/) )

  proof
    cA
    cB
    cin
    c0
    wceq
    #
    vx
    cA
    vx
    cv
    csn
    cC
    cxp
    ciun
    #
    cA
    cvv
    cxp
    #
    wss
    @2
    vy
    cB
    vy
    cv
    csn
    cD
    cxp
    ciun
    #
    cin
    #
    c0
    wceq
    @1
    @3
    cin
    c0
    wceq
    vx
    cA
    cC
    djussxp
    @0
    @4
    @3
    @2
    cin
    #
    c0
    @2
    @3
    incom
    @0
    @3
    cB
    cvv
    cxp
    #
    wss
    @6
    @2
    cin
    #
    c0
    wceq
    @5
    c0
    wceq
    vy
    cB
    cD
    djussxp
    @0
    @7
    @2
    @6
    cin
    c0
    @6
    @2
    incom
    cA
    cB
    cvv
    cvv
    xpdisj1
    syl5eq
    @3
    @6
    @2
    ssdisj
    sylancr
    syl5eq
    @1
    @2
    @3
    ssdisj
    sylancr
end
