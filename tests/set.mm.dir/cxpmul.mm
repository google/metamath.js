include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cc.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "ce.mm"
include "ccxp.mm"
include "simp3.mm"
include "simp2.mm"
include "recnd.mm"
include "relogcl.mm"
include "3ad2ant1.mm"
include "mulassd.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "rpcn.mm"
include "rpne0.mm"
include "cxpef.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "remulcld.mm"
include "relogefd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "mulcld.mm"
include "cxpcl.mm"
include "syl2anc.mm"
include "cxpne0.mm"

theorem cxpmul
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR+ /\ B e. RR /\ C e. CC ) -> ( A ^c ( B x. C ) ) = ( ( A ^c B ) ^c C ) )

  proof
    cA
    crp
    wcel
    #
    cB
    cr
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
    cmul
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
    cC
    cA
    cB
    ccxp
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cA
    @4
    ccxp
    co
    #
    @8
    cC
    ccxp
    co
    #
    @3
    @6
    @10
    ce
    @3
    cC
    cB
    cmul
    co
    #
    @5
    cmul
    co
    cC
    cB
    @5
    cmul
    co
    #
    cmul
    co
    @6
    @10
    @3
    cC
    cB
    @5
    @0
    @1
    @2
    simp3
    #
    @3
    cB
    @0
    @1
    @2
    simp2
    #
    recnd
    #
    @3
    @5
    @0
    @1
    @5
    cr
    wcel
    @2
    cA
    relogcl
    3ad2ant1
    #
    recnd
    mulassd
    @3
    @4
    @14
    @5
    cmul
    @3
    cB
    cC
    @18
    @16
    mulcomd
    oveq1d
    @3
    @9
    @15
    cC
    cmul
    @3
    @9
    @15
    ce
    cfv
    #
    clog
    cfv
    @15
    @3
    @8
    @20
    clog
    @3
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cB
    cc
    wcel
    #
    @8
    @20
    wceq
    @0
    @1
    @21
    @2
    cA
    rpcn
    3ad2ant1
    #
    @0
    @1
    @22
    @2
    cA
    rpne0
    3ad2ant1
    #
    @18
    cA
    cB
    cxpef
    syl3anc
    fveq2d
    @3
    @15
    @3
    cB
    @5
    @17
    @19
    remulcld
    relogefd
    eqtrd
    oveq2d
    3eqtr4d
    fveq2d
    @3
    @21
    @22
    @4
    cc
    wcel
    @12
    @7
    wceq
    @24
    @25
    @3
    cB
    cC
    @18
    @16
    mulcld
    cA
    @4
    cxpef
    syl3anc
    @3
    @8
    cc
    wcel
    #
    @8
    cc0
    wne
    #
    @2
    @13
    @11
    wceq
    @3
    @21
    @23
    @26
    @24
    @18
    cA
    cB
    cxpcl
    syl2anc
    @3
    @21
    @22
    @23
    @27
    @24
    @25
    @18
    cA
    cB
    cxpne0
    syl3anc
    @16
    @8
    cC
    cxpef
    syl3anc
    3eqtr4d
end
