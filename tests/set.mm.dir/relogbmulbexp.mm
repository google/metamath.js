include "crp.mm"
include "c1.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "ccxp.mm"
include "co.mm"
include "cmul.mm"
include "clogb.mm"
include "caddc.mm"
include "cc.mm"
include "cc0.mm"
include "cpr.mm"
include "wceq.mm"
include "wne.mm"
include "w3a.mm"
include "rpcn.mm"
include "adantr.mm"
include "rpne0.mm"
include "simpr.mm"
include "3jca.mm"
include "eldifsn.mm"
include "eldifpr.mm"
include "3imtr4i.mm"
include "simprl.mm"
include "eldifi.mm"
include "adantl.mm"
include "relogbmulexp.mm"
include "syl13anc.mm"
include "sylbi.mm"
include "logbid1.mm"
include "syl.mm"
include "oveq2d.mm"
include "ax-1rid.mm"
include "eqtrd.mm"

theorem relogbmulbexp
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( B e. ( RR+ \ { 1 } ) /\ ( A e. RR+ /\ C e. RR ) ) -> ( B logb ( A x. ( B ^c C ) ) ) = ( ( B logb A ) + C ) )

  proof
    cB
    crp
    c1
    csn
    #
    cdif
    wcel
    #
    cA
    crp
    wcel
    #
    cC
    cr
    wcel
    #
    wa
    #
    wa
    #
    cB
    cA
    cB
    cC
    ccxp
    co
    cmul
    co
    clogb
    co
    #
    cB
    cA
    clogb
    co
    #
    cC
    cB
    cB
    clogb
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @7
    cC
    caddc
    co
    @5
    cB
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    @2
    cB
    crp
    wcel
    #
    @3
    @6
    @10
    wceq
    @1
    @11
    @4
    @12
    cB
    c1
    wne
    #
    wa
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    @13
    w3a
    #
    @1
    @11
    @14
    @15
    @16
    @13
    @12
    @15
    @13
    cB
    rpcn
    adantr
    @12
    @16
    @13
    cB
    rpne0
    adantr
    @12
    @13
    simpr
    3jca
    #
    cB
    crp
    c1
    eldifsn
    #
    cB
    cc
    cc0
    c1
    eldifpr
    3imtr4i
    adantr
    @1
    @2
    @3
    simprl
    @1
    @12
    @4
    cB
    crp
    @0
    eldifi
    adantr
    @4
    @3
    @1
    @2
    @3
    simpr
    adantl
    cA
    cB
    cB
    cC
    relogbmulexp
    syl13anc
    @5
    @9
    cC
    @7
    caddc
    @5
    @9
    cC
    c1
    cmul
    co
    #
    cC
    @5
    @8
    c1
    cC
    cmul
    @1
    @8
    c1
    wceq
    #
    @4
    @1
    @17
    @21
    @1
    @14
    @17
    @19
    @18
    sylbi
    cB
    logbid1
    syl
    adantr
    oveq2d
    @4
    @20
    cC
    wceq
    #
    @1
    @3
    @22
    @2
    cC
    ax-1rid
    adantl
    adantl
    eqtrd
    oveq2d
    eqtrd
end
