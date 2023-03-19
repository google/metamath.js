include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "wne.mm"
include "wa.mm"
include "cr.mm"
include "w3a.mm"
include "clogb.mm"
include "co.mm"
include "wceq.mm"
include "ccxp.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "cc.mm"
include "cc0.mm"
include "cpr.mm"
include "cdif.mm"
include "csn.mm"
include "rpcn.mm"
include "adantr.mm"
include "rpne0.mm"
include "simpr.mm"
include "eldifpr.mm"
include "syl3anbrc.mm"
include "rpcndif0.mm"
include "anim12i.mm"
include "3adant3.mm"
include "cxplogb.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "eldifsn.mm"
include "biimpri.mm"
include "anim1i.mm"
include "3adant2.mm"
include "relogbcxp.mm"
include "impbida.mm"

theorem relogbcxpb
  let cB: class B
  let cX: class X
  let cY: class Y


  assert |- ( ( ( B e. RR+ /\ B =/= 1 ) /\ X e. RR+ /\ Y e. RR ) -> ( ( B logb X ) = Y <-> ( B ^c Y ) = X ) )

  proof
    cB
    crp
    wcel
    #
    cB
    c1
    wne
    #
    wa
    #
    cX
    crp
    wcel
    #
    cY
    cr
    wcel
    #
    w3a
    #
    cB
    cX
    clogb
    co
    #
    cY
    wceq
    #
    cB
    cY
    ccxp
    co
    #
    cX
    wceq
    #
    @7
    @5
    @8
    cB
    @6
    ccxp
    co
    #
    cX
    @8
    @10
    wceq
    cY
    @6
    cY
    @6
    cB
    ccxp
    oveq2
    eqcoms
    @5
    cB
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    cX
    cc
    cc0
    csn
    cdif
    wcel
    #
    wa
    #
    @10
    cX
    wceq
    @2
    @3
    @13
    @4
    @2
    @11
    @3
    @12
    @2
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    @1
    @11
    @0
    @14
    @1
    cB
    rpcn
    adantr
    @0
    @15
    @1
    cB
    rpne0
    adantr
    @0
    @1
    simpr
    cB
    cc
    cc0
    c1
    eldifpr
    syl3anbrc
    cX
    rpcndif0
    anim12i
    3adant3
    cB
    cX
    cxplogb
    syl
    sylan9eqr
    @9
    @5
    @6
    cB
    @8
    clogb
    co
    #
    cY
    @6
    @16
    wceq
    cX
    @8
    cX
    @8
    cB
    clogb
    oveq2
    eqcoms
    @5
    cB
    crp
    c1
    csn
    cdif
    wcel
    #
    @4
    wa
    #
    @16
    cY
    wceq
    @2
    @4
    @18
    @3
    @2
    @17
    @4
    @17
    @2
    cB
    crp
    c1
    eldifsn
    biimpri
    anim1i
    3adant2
    cB
    cY
    relogbcxp
    syl
    sylan9eqr
    impbida
end
