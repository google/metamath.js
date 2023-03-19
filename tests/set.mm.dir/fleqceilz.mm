include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "cfl.mm"
include "cfv.mm"
include "cceil.mm"
include "wceq.mm"
include "flid.mm"
include "ceilid.mm"
include "eqtr4d.mm"
include "wi.mm"
include "wa.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantr.mm"
include "ceilidz.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "biimprd.mm"
include "adantl.mm"
include "sylbid.mm"
include "ex.mm"
include "wn.mm"
include "cle.mm"
include "wbr.mm"
include "flle.mm"
include "wne.mm"
include "df-ne.mm"
include "necom.mm"
include "clt.mm"
include "reflcl.mm"
include "id.mm"
include "ltlend.mm"
include "breq1.mm"
include "ceilge.mm"
include "ceilcl.mm"
include "zred.mm"
include "lenltd.mm"
include "pm2.21.mm"
include "syl6bi.mm"
include "mpd.mm"
include "com23.mm"
include "sylbird.mm"
include "expd.mm"
include "com3r.mm"
include "sylbi.mm"
include "sylbir.mm"
include "mpdi.mm"
include "pm2.61i.mm"
include "impbid2.mm"

theorem fleqceilz
  let cA: class A


  assert |- ( A e. RR -> ( A e. ZZ <-> ( |_ ` A ) = ( |^ ` A ) ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cz
    wcel
    #
    cA
    cfl
    cfv
    #
    cA
    cceil
    cfv
    #
    wceq
    #
    @1
    @2
    cA
    @3
    cA
    flid
    cA
    ceilid
    eqtr4d
    @2
    cA
    wceq
    #
    @0
    @4
    @1
    wi
    #
    wi
    @5
    @0
    @6
    @5
    @0
    wa
    @4
    cA
    @3
    wceq
    #
    @1
    @5
    @4
    @7
    wb
    @0
    @2
    cA
    @3
    eqeq1
    adantr
    @0
    @7
    @1
    wi
    @5
    @0
    @1
    @7
    @0
    @1
    @3
    cA
    wceq
    @7
    cA
    ceilidz
    @3
    cA
    eqcom
    syl6bb
    biimprd
    adantl
    sylbid
    ex
    @5
    wn
    #
    @0
    @2
    cA
    cle
    wbr
    #
    @6
    cA
    flle
    @8
    @2
    cA
    wne
    #
    @0
    @9
    @6
    wi
    wi
    #
    @2
    cA
    df-ne
    @10
    cA
    @2
    wne
    #
    @11
    @2
    cA
    necom
    @0
    @9
    @12
    @6
    @0
    @9
    @12
    @6
    @0
    @9
    @12
    wa
    @2
    cA
    clt
    wbr
    #
    @6
    @0
    @2
    cA
    cA
    reflcl
    @0
    id
    #
    ltlend
    @0
    @4
    @13
    @1
    @0
    @4
    @13
    @1
    wi
    @0
    @4
    wa
    @13
    @3
    cA
    clt
    wbr
    #
    @1
    @4
    @13
    @15
    wb
    @0
    @2
    @3
    cA
    clt
    breq1
    adantl
    @0
    @15
    @1
    wi
    #
    @4
    @0
    cA
    @3
    cle
    wbr
    #
    @16
    cA
    ceilge
    @0
    @17
    @15
    wn
    @16
    @0
    cA
    @3
    @14
    @0
    @3
    cA
    ceilcl
    zred
    lenltd
    @15
    @1
    pm2.21
    syl6bi
    mpd
    adantr
    sylbid
    ex
    com23
    sylbird
    expd
    com3r
    sylbi
    sylbir
    mpdi
    pm2.61i
    impbid2
end
