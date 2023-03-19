include "wcel.mm"
include "wa.mm"
include "cpm.mm"
include "co.mm"
include "wfun.mm"
include "cxp.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "crab.mm"
include "pmvalg.mm"
include "eleq2d.mm"
include "funeq.mm"
include "elrab.mm"
include "syl6bb.mm"
include "ancom.mm"
include "cvv.mm"
include "wi.mm"
include "elex.mm"
include "a1i.mm"
include "xpexg.mm"
include "ancoms.mm"
include "ssexg.mm"
include "expcom.mm"
include "syl.mm"
include "wb.mm"
include "elpwg.mm"
include "pm5.21ndd.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem elpmg
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let vg: setvar g


  assert |- ( ( A e. V /\ B e. W ) -> ( C e. ( A ^pm B ) <-> ( Fun C /\ C C_ ( B X. A ) ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cC
    cA
    cB
    cpm
    co
    #
    wcel
    #
    cC
    wfun
    #
    cC
    cB
    cA
    cxp
    #
    cpw
    #
    wcel
    #
    wa
    #
    @5
    cC
    @6
    wss
    #
    wa
    @2
    @4
    @8
    @5
    wa
    #
    @9
    @2
    @4
    cC
    vg
    cv
    #
    wfun
    #
    vg
    @7
    crab
    #
    wcel
    @11
    @2
    @3
    @14
    cC
    cA
    cB
    cV
    cW
    vg
    pmvalg
    eleq2d
    @13
    @5
    vg
    cC
    @7
    @12
    cC
    funeq
    elrab
    syl6bb
    @8
    @5
    ancom
    syl6bb
    @2
    @8
    @10
    @5
    @2
    cC
    cvv
    wcel
    #
    @8
    @10
    @8
    @15
    wi
    @2
    cC
    @7
    elex
    a1i
    @2
    @6
    cvv
    wcel
    #
    @10
    @15
    wi
    @1
    @0
    @16
    cB
    cA
    cW
    cV
    xpexg
    ancoms
    @10
    @16
    @15
    cC
    @6
    cvv
    ssexg
    expcom
    syl
    @15
    @8
    @10
    wb
    wi
    @2
    cC
    @6
    cvv
    elpwg
    a1i
    pm5.21ndd
    anbi2d
    bitrd
end
