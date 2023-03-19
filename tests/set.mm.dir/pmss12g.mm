include "wss.mm"
include "wa.mm"
include "wcel.mm"
include "cpm.mm"
include "co.mm"
include "cv.mm"
include "wfun.mm"
include "cxp.mm"
include "wi.mm"
include "xpss12.mm"
include "ancoms.mm"
include "sstr.mm"
include "expcom.mm"
include "syl.mm"
include "anim2d.mm"
include "adantr.mm"
include "wb.mm"
include "cvv.mm"
include "ssexg.mm"
include "elpmg.mm"
include "syl2an.mm"
include "an4s.mm"
include "adantl.mm"
include "3imtr4d.mm"
include "ssrdv.mm"

theorem pmss12g
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  let vf: setvar f


  assert |- ( ( ( A C_ C /\ B C_ D ) /\ ( C e. V /\ D e. W ) ) -> ( A ^pm B ) C_ ( C ^pm D ) )

  proof
    cA
    cC
    wss
    #
    cB
    cD
    wss
    #
    wa
    #
    cC
    cV
    wcel
    #
    cD
    cW
    wcel
    #
    wa
    #
    wa
    #
    vf
    cA
    cB
    cpm
    co
    #
    cC
    cD
    cpm
    co
    #
    @6
    vf
    cv
    #
    wfun
    #
    @9
    cB
    cA
    cxp
    #
    wss
    #
    wa
    #
    @10
    @9
    cD
    cC
    cxp
    #
    wss
    #
    wa
    #
    @9
    @7
    wcel
    #
    @9
    @8
    wcel
    #
    @2
    @13
    @16
    wi
    @5
    @2
    @12
    @15
    @10
    @2
    @11
    @14
    wss
    #
    @12
    @15
    wi
    @1
    @0
    @19
    cB
    cD
    cA
    cC
    xpss12
    ancoms
    @12
    @19
    @15
    @9
    @11
    @14
    sstr
    expcom
    syl
    anim2d
    adantr
    @0
    @3
    @1
    @4
    @17
    @13
    wb
    #
    @0
    @3
    wa
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    @20
    @1
    @4
    wa
    cA
    cC
    cV
    ssexg
    cB
    cD
    cW
    ssexg
    cA
    cB
    @9
    cvv
    cvv
    elpmg
    syl2an
    an4s
    @5
    @18
    @16
    wb
    @2
    cC
    cD
    @9
    cV
    cW
    elpmg
    adantl
    3imtr4d
    ssrdv
end
