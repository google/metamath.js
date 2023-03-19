include "wcel.mm"
include "wn.mm"
include "csn.mm"
include "cun.mm"
include "ccrd.mm"
include "cfv.mm"
include "csuc.mm"
include "cen.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wbr.mm"
include "disjsn.mm"
include "word.mm"
include "cardon.mm"
include "onordi.mm"
include "orddisj.mm"
include "ax-mp.mm"
include "wa.mm"
include "cardid.mm"
include "ensymi.mm"
include "cvv.mm"
include "fvex.mm"
include "en2sn.mm"
include "mp2an.mm"
include "unen.mm"
include "mpanl12.mm"
include "mpan2.mm"
include "sylbir.mm"
include "df-suc.mm"
include "syl6breqr.mm"

theorem unsnen
  let cA: class A
  let cB: class B
  assume unsnen.1: |- A e. _V
  assume unsnen.2: |- B e. _V


  assert |- ( -. B e. A -> ( A u. { B } ) ~~ suc ( card ` A ) )

  proof
    cB
    cA
    wcel
    wn
    #
    cA
    cB
    csn
    #
    cun
    #
    cA
    ccrd
    cfv
    #
    @3
    csn
    #
    cun
    #
    @3
    csuc
    cen
    @0
    cA
    @1
    cin
    c0
    wceq
    #
    @2
    @5
    cen
    wbr
    #
    cA
    cB
    disjsn
    @6
    @3
    @4
    cin
    c0
    wceq
    #
    @7
    @3
    word
    @8
    @3
    cA
    cardon
    onordi
    @3
    orddisj
    ax-mp
    cA
    @3
    cen
    wbr
    @1
    @4
    cen
    wbr
    #
    @6
    @8
    wa
    @7
    @3
    cA
    cA
    unsnen.1
    cardid
    ensymi
    cB
    cvv
    wcel
    @3
    cvv
    wcel
    @9
    unsnen.2
    cA
    ccrd
    fvex
    cB
    @3
    cvv
    cvv
    en2sn
    mp2an
    cA
    @3
    @1
    @4
    unen
    mpanl12
    mpan2
    sylbir
    @3
    df-suc
    syl6breqr
end
