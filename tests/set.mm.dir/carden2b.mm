include "cen.mm"
include "wbr.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "wss.mm"
include "cardne.mm"
include "ennum.mm"
include "biimpa.mm"
include "cardid2.mm"
include "syl.mm"
include "ensym.mm"
include "adantr.mm"
include "entr.mm"
include "syl2anc.mm"
include "nsyl3.mm"
include "con0.mm"
include "wb.mm"
include "cardon.mm"
include "ontri1.mm"
include "mp2an.mm"
include "sylibr.mm"
include "id.mm"
include "syl2anr.mm"
include "eqssd.mm"
include "c0.mm"
include "ndmfv.mm"
include "adantl.mm"
include "notbid.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"

theorem carden2b
  let cA: class A
  let cB: class B


  assert |- ( A ~~ B -> ( card ` A ) = ( card ` B ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cA
    ccrd
    cdm
    #
    wcel
    #
    cA
    ccrd
    cfv
    #
    cB
    ccrd
    cfv
    #
    wceq
    @0
    @2
    wa
    #
    @3
    @4
    @5
    @4
    @3
    wcel
    #
    wn
    #
    @3
    @4
    wss
    #
    @6
    @4
    cA
    cen
    wbr
    #
    @5
    @4
    cA
    cardne
    @5
    @4
    cB
    cen
    wbr
    #
    cB
    cA
    cen
    wbr
    #
    @9
    @5
    cB
    @1
    wcel
    #
    @10
    @0
    @2
    @12
    cA
    cB
    ennum
    #
    biimpa
    cB
    cardid2
    syl
    @0
    @11
    @2
    cA
    cB
    ensym
    adantr
    @4
    cB
    cA
    entr
    syl2anc
    nsyl3
    @3
    con0
    wcel
    #
    @4
    con0
    wcel
    #
    @8
    @7
    wb
    cA
    cardon
    #
    cB
    cardon
    #
    @3
    @4
    ontri1
    mp2an
    sylibr
    @5
    @3
    @4
    wcel
    #
    wn
    #
    @4
    @3
    wss
    #
    @18
    @3
    cB
    cen
    wbr
    #
    @5
    @3
    cB
    cardne
    @2
    @3
    cA
    cen
    wbr
    @0
    @21
    @0
    cA
    cardid2
    @0
    id
    @3
    cA
    cB
    entr
    syl2anr
    nsyl3
    @15
    @14
    @20
    @19
    wb
    @17
    @16
    @4
    @3
    ontri1
    mp2an
    sylibr
    eqssd
    @0
    @2
    wn
    #
    wa
    #
    @3
    c0
    @4
    @22
    @3
    c0
    wceq
    @0
    cA
    ccrd
    ndmfv
    adantl
    @23
    @12
    wn
    #
    @4
    c0
    wceq
    @0
    @22
    @24
    @0
    @2
    @12
    @13
    notbid
    biimpa
    cB
    ccrd
    ndmfv
    syl
    eqtr4d
    pm2.61dan
end
