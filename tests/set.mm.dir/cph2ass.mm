include "ccph.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cmul.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2r.mm"
include "simp3l.mm"
include "simp3r.mm"
include "cphassr.mm"
include "syl13anc.mm"
include "oveq2d.mm"
include "simp2l.mm"
include "clmod.mm"
include "cphlmod.mm"
include "3ad2ant1.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "cphass.mm"
include "cc.mm"
include "cclm.mm"
include "wss.mm"
include "cphclm.mm"
include "clmsscn.mm"
include "syl.mm"
include "sseldd.mm"
include "cjcld.mm"
include "cphipcl.mm"
include "3expb.mm"
include "3adant2.mm"
include "mulassd.mm"
include "3eqtr4d.mm"

theorem cph2ass
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.x: class .x.
  let cF: class F
  let c.xi: class .,
  let cK: class K
  let cV: class V
  let cW: class W
  assume cphipcj.h: |- ., = ( .i ` W )
  assume cphipcj.v: |- V = ( Base ` W )
  assume cphass.f: |- F = ( Scalar ` W )
  assume cphass.k: |- K = ( Base ` F )
  assume cphass.s: |- .x. = ( .s ` W )


  assert |- ( ( W e. CPreHil /\ ( A e. K /\ B e. K ) /\ ( C e. V /\ D e. V ) ) -> ( ( A .x. C ) ., ( B .x. D ) ) = ( ( A x. ( * ` B ) ) x. ( C ., D ) ) )

  proof
    cW
    ccph
    wcel
    #
    cA
    cK
    wcel
    #
    cB
    cK
    wcel
    #
    wa
    #
    cC
    cV
    wcel
    #
    cD
    cV
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cC
    cB
    cD
    c.x
    co
    #
    c.xi
    co
    #
    cmul
    co
    #
    cA
    cB
    ccj
    cfv
    #
    cC
    cD
    c.xi
    co
    #
    cmul
    co
    #
    cmul
    co
    cA
    cC
    c.x
    co
    @8
    c.xi
    co
    #
    cA
    @11
    cmul
    co
    @12
    cmul
    co
    @7
    @9
    @13
    cA
    cmul
    @7
    @0
    @2
    @4
    @5
    @9
    @13
    wceq
    @0
    @3
    @6
    simp1
    #
    @0
    @1
    @2
    @6
    simp2r
    #
    @0
    @3
    @4
    @5
    simp3l
    #
    @0
    @3
    @4
    @5
    simp3r
    #
    cB
    cC
    cD
    c.x
    cF
    c.xi
    cK
    cV
    cW
    cphipcj.h
    cphipcj.v
    cphass.f
    cphass.k
    cphass.s
    cphassr
    syl13anc
    oveq2d
    @7
    @0
    @1
    @4
    @8
    cV
    wcel
    #
    @14
    @10
    wceq
    @15
    @0
    @1
    @2
    @6
    simp2l
    #
    @17
    @7
    cW
    clmod
    wcel
    #
    @2
    @5
    @19
    @0
    @3
    @21
    @6
    cW
    cphlmod
    3ad2ant1
    @16
    @18
    cB
    c.x
    cF
    cK
    cV
    cW
    cD
    cphipcj.v
    cphass.f
    cphass.s
    cphass.k
    lmodvscl
    syl3anc
    cA
    cC
    @8
    c.x
    cF
    c.xi
    cK
    cV
    cW
    cphipcj.h
    cphipcj.v
    cphass.f
    cphass.k
    cphass.s
    cphass
    syl13anc
    @7
    cA
    @11
    @12
    @7
    cK
    cc
    cA
    @7
    cW
    cclm
    wcel
    #
    cK
    cc
    wss
    @0
    @3
    @22
    @6
    cW
    cphclm
    3ad2ant1
    cF
    cK
    cW
    cphass.f
    cphass.k
    clmsscn
    syl
    #
    @20
    sseldd
    @7
    cB
    @7
    cK
    cc
    cB
    @23
    @16
    sseldd
    cjcld
    @0
    @6
    @12
    cc
    wcel
    #
    @3
    @0
    @4
    @5
    @24
    cC
    cD
    c.xi
    cV
    cW
    cphipcj.v
    cphipcj.h
    cphipcl
    3expb
    3adant2
    mulassd
    3eqtr4d
end
