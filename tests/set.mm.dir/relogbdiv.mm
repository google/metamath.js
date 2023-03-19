include "cc.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cdif.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cneg.mm"
include "ccxp.mm"
include "co.mm"
include "cmul.mm"
include "clogb.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmin.mm"
include "cr.mm"
include "wceq.mm"
include "neg1rr.mm"
include "relogbmulexp.mm"
include "mp3anr3.mm"
include "rpcn.mm"
include "adantr.mm"
include "adantl.mm"
include "wne.mm"
include "rpne0.mm"
include "divrecd.mm"
include "1cnd.mm"
include "cxpnegd.mm"
include "cxp1d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "csn.mm"
include "rpcndif0.mm"
include "logbcl.mm"
include "sylan2.mm"
include "mulm1.mm"
include "syl.mm"
include "negsubd.mm"
include "eqtr2d.mm"
include "3eqtr4d.mm"

theorem relogbdiv
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( B e. ( CC \ { 0 , 1 } ) /\ ( A e. RR+ /\ C e. RR+ ) ) -> ( B logb ( A / C ) ) = ( ( B logb A ) - ( B logb C ) ) )

  proof
    cB
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    cA
    crp
    wcel
    #
    cC
    crp
    wcel
    #
    wa
    #
    wa
    #
    cB
    cA
    cC
    c1
    cneg
    #
    ccxp
    co
    #
    cmul
    co
    #
    clogb
    co
    #
    cB
    cA
    clogb
    co
    #
    @5
    cB
    cC
    clogb
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cB
    cA
    cC
    cdiv
    co
    #
    clogb
    co
    @9
    @10
    cmin
    co
    #
    @0
    @1
    @2
    @5
    cr
    wcel
    @8
    @12
    wceq
    neg1rr
    cA
    cB
    cC
    @5
    relogbmulexp
    mp3anr3
    @4
    @13
    @7
    cB
    clogb
    @3
    @13
    @7
    wceq
    @0
    @3
    @13
    cA
    c1
    cC
    cdiv
    co
    #
    cmul
    co
    @7
    @3
    cA
    cC
    @1
    cA
    cc
    wcel
    @2
    cA
    rpcn
    adantr
    @2
    cC
    cc
    wcel
    @1
    cC
    rpcn
    #
    adantl
    @2
    cC
    cc0
    wne
    @1
    cC
    rpne0
    #
    adantl
    divrecd
    @3
    @6
    @15
    cA
    cmul
    @2
    @6
    @15
    wceq
    @1
    @2
    @6
    c1
    cC
    c1
    ccxp
    co
    #
    cdiv
    co
    @15
    @2
    cC
    c1
    @16
    @17
    @2
    1cnd
    cxpnegd
    @2
    @18
    cC
    c1
    cdiv
    @2
    cC
    @16
    cxp1d
    oveq2d
    eqtrd
    adantl
    oveq2d
    eqtr4d
    adantl
    oveq2d
    @4
    @12
    @9
    @10
    cneg
    #
    caddc
    co
    #
    @14
    @4
    @10
    cc
    wcel
    #
    @12
    @20
    wceq
    @3
    @0
    cC
    cc
    cc0
    csn
    cdif
    #
    wcel
    #
    @21
    @2
    @23
    @1
    cC
    rpcndif0
    adantl
    cB
    cC
    logbcl
    sylan2
    #
    @21
    @11
    @19
    @9
    caddc
    @10
    mulm1
    oveq2d
    syl
    @4
    @9
    @10
    @3
    @0
    cA
    @22
    wcel
    #
    @9
    cc
    wcel
    @1
    @25
    @2
    cA
    rpcndif0
    adantr
    cB
    cA
    logbcl
    sylan2
    @24
    negsubd
    eqtr2d
    3eqtr4d
end
