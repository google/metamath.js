include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wss.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "c0.mm"
include "wceq.mm"
include "wb.mm"
include "cardnueq0.mm"
include "adantr.mm"
include "biimpa.mm"
include "0domg.mm"
include "ad2antlr.mm"
include "eqbrtrd.mm"
include "a1d.mm"
include "wne.mm"
include "cvv.mm"
include "fvex.mm"
include "simprr.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "cen.mm"
include "cardid2.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "ssn0.mm"
include "syl2anc.mm"
include "ndmfv.mm"
include "necon1ai.mm"
include "3syl.mm"
include "domen1.mm"
include "domen2.mm"
include "sylan9bb.mm"
include "mpbid.mm"
include "expr.mm"
include "pm2.61dane.mm"

theorem carddomi2
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( ( A e. dom card /\ B e. V ) -> ( ( card ` A ) C_ ( card ` B ) -> A ~<_ B ) )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    cA
    ccrd
    cfv
    #
    cB
    ccrd
    cfv
    #
    wss
    #
    cA
    cB
    cdom
    wbr
    #
    wi
    @4
    c0
    @3
    @4
    c0
    wceq
    #
    wa
    #
    @7
    @6
    @9
    cA
    c0
    cB
    cdom
    @3
    @8
    cA
    c0
    wceq
    #
    @1
    @8
    @10
    wb
    @2
    cA
    cardnueq0
    adantr
    biimpa
    @2
    c0
    cB
    cdom
    wbr
    @1
    @8
    cB
    cV
    0domg
    ad2antlr
    eqbrtrd
    a1d
    @3
    @4
    c0
    wne
    #
    @6
    @7
    @3
    @11
    @6
    wa
    #
    wa
    #
    @4
    @5
    cdom
    wbr
    #
    @7
    @5
    cvv
    wcel
    @13
    @6
    @14
    cB
    ccrd
    fvex
    @3
    @11
    @6
    simprr
    #
    @4
    @5
    cvv
    ssdomg
    mpsyl
    @13
    @4
    cA
    cen
    wbr
    #
    @5
    cB
    cen
    wbr
    #
    @14
    @7
    wb
    @1
    @16
    @2
    @12
    cA
    cardid2
    ad2antrr
    @13
    @5
    c0
    wne
    #
    cB
    @0
    wcel
    #
    @17
    @13
    @6
    @11
    @18
    @15
    @3
    @11
    @6
    simprl
    @4
    @5
    ssn0
    syl2anc
    @19
    @5
    c0
    cB
    ccrd
    ndmfv
    necon1ai
    cB
    cardid2
    3syl
    @16
    @14
    cA
    @5
    cdom
    wbr
    @17
    @7
    @4
    cA
    @5
    domen1
    @5
    cB
    cA
    domen2
    sylan9bb
    syl2anc
    mpbid
    expr
    pm2.61dane
end
