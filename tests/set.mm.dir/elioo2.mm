include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "crab.mm"
include "w3a.mm"
include "iooval2.mm"
include "eleq2d.mm"
include "wceq.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "elrab.mm"
include "3anass.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem elioo2
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( C e. ( A (,) B ) <-> ( C e. RR /\ A < C /\ C < B ) ) )

  proof
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    wa
    #
    cC
    cA
    cB
    cioo
    co
    #
    wcel
    cC
    cA
    vx
    cv
    #
    clt
    wbr
    #
    @2
    cB
    clt
    wbr
    #
    wa
    #
    vx
    cr
    crab
    #
    wcel
    #
    cC
    cr
    wcel
    #
    cA
    cC
    clt
    wbr
    #
    cC
    cB
    clt
    wbr
    #
    w3a
    #
    @0
    @1
    @6
    cC
    vx
    cA
    cB
    iooval2
    eleq2d
    @7
    @8
    @9
    @10
    wa
    #
    wa
    @11
    @5
    @12
    vx
    cC
    cr
    @2
    cC
    wceq
    @3
    @9
    @4
    @10
    @2
    cC
    cA
    clt
    breq2
    @2
    cC
    cB
    clt
    breq1
    anbi12d
    elrab
    @8
    @9
    @10
    3anass
    bitr4i
    syl6bb
end
