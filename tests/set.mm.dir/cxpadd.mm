include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "ce.mm"
include "ccxp.mm"
include "simp2.mm"
include "simp3.mm"
include "logcl.mm"
include "3ad2ant1.mm"
include "adddird.mm"
include "fveq2d.mm"
include "wceq.mm"
include "mulcld.mm"
include "efadd.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "simp1l.mm"
include "simp1r.mm"
include "addcl.mm"
include "3adant1.mm"
include "cxpef.mm"
include "syl3anc.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem cxpadd
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ B e. CC /\ C e. CC ) -> ( A ^c ( B + C ) ) = ( ( A ^c B ) x. ( A ^c C ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    w3a
    #
    cB
    cC
    caddc
    co
    #
    cA
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cB
    @7
    cmul
    co
    #
    ce
    cfv
    #
    cC
    @7
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    cA
    @6
    ccxp
    co
    #
    cA
    cB
    ccxp
    co
    #
    cA
    cC
    ccxp
    co
    #
    cmul
    co
    @5
    @9
    @10
    @12
    caddc
    co
    #
    ce
    cfv
    #
    @14
    @5
    @8
    @18
    ce
    @5
    cB
    cC
    @7
    @2
    @3
    @4
    simp2
    #
    @2
    @3
    @4
    simp3
    #
    @2
    @3
    @7
    cc
    wcel
    @4
    cA
    logcl
    3ad2ant1
    #
    adddird
    fveq2d
    @5
    @10
    cc
    wcel
    @12
    cc
    wcel
    @19
    @14
    wceq
    @5
    cB
    @7
    @20
    @22
    mulcld
    @5
    cC
    @7
    @21
    @22
    mulcld
    @10
    @12
    efadd
    syl2anc
    eqtrd
    @5
    @0
    @1
    @6
    cc
    wcel
    #
    @15
    @9
    wceq
    @0
    @1
    @3
    @4
    simp1l
    #
    @0
    @1
    @3
    @4
    simp1r
    #
    @3
    @4
    @23
    @2
    cB
    cC
    addcl
    3adant1
    cA
    @6
    cxpef
    syl3anc
    @5
    @16
    @11
    @17
    @13
    cmul
    @5
    @0
    @1
    @3
    @16
    @11
    wceq
    @24
    @25
    @20
    cA
    cB
    cxpef
    syl3anc
    @5
    @0
    @1
    @4
    @17
    @13
    wceq
    @24
    @25
    @21
    cA
    cC
    cxpef
    syl3anc
    oveq12d
    3eqtr4d
end
