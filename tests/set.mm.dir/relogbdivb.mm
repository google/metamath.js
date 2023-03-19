include "crp.mm"
include "c1.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "clogb.mm"
include "cmin.mm"
include "cc.mm"
include "cc0.mm"
include "cpr.mm"
include "wceq.mm"
include "wne.mm"
include "w3a.mm"
include "eldifsn.mm"
include "rpcn.mm"
include "adantr.mm"
include "rpne0.mm"
include "simpr.mm"
include "3jca.mm"
include "sylbi.mm"
include "eldifpr.mm"
include "sylibr.mm"
include "eldifi.mm"
include "relogbdiv.mm"
include "syl12anc.mm"
include "logbid1.mm"
include "syl.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem relogbdivb
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( B e. ( RR+ \ { 1 } ) /\ A e. RR+ ) -> ( B logb ( A / B ) ) = ( ( B logb A ) - 1 ) )

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
    wa
    #
    cB
    cA
    cB
    cdiv
    co
    clogb
    co
    #
    cB
    cA
    clogb
    co
    #
    cB
    cB
    clogb
    co
    #
    cmin
    co
    #
    @5
    c1
    cmin
    co
    @3
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
    @4
    @7
    wceq
    @1
    @8
    @2
    @1
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    cB
    c1
    wne
    #
    w3a
    #
    @8
    @1
    @9
    @12
    wa
    #
    @13
    cB
    crp
    c1
    eldifsn
    @14
    @10
    @11
    @12
    @9
    @10
    @12
    cB
    rpcn
    adantr
    @9
    @11
    @12
    cB
    rpne0
    adantr
    @9
    @12
    simpr
    3jca
    sylbi
    #
    cB
    cc
    cc0
    c1
    eldifpr
    sylibr
    adantr
    @1
    @2
    simpr
    @1
    @9
    @2
    cB
    crp
    @0
    eldifi
    adantr
    cA
    cB
    cB
    relogbdiv
    syl12anc
    @3
    @6
    c1
    @5
    cmin
    @1
    @6
    c1
    wceq
    #
    @2
    @1
    @13
    @16
    @15
    cB
    logbid1
    syl
    adantr
    oveq2d
    eqtrd
end
