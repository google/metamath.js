include "con0.mm"
include "wcel.mm"
include "cale.mm"
include "cfv.mm"
include "cdom.mm"
include "wbr.mm"
include "csuc.mm"
include "csdm.mm"
include "alephordilem1.mm"
include "domsdomtr.mm"
include "ex.mm"
include "syl5com.mm"
include "ccrd.mm"
include "cen.mm"
include "cdm.mm"
include "sdomdom.mm"
include "alephon.mm"
include "ondomen.mm"
include "mpan.mm"
include "cardid2.mm"
include "3syl.mm"
include "ensymd.mm"
include "wn.mm"
include "alephnbtwn2.mm"
include "imnani.mm"
include "ensdomtr.mm"
include "mpancom.mm"
include "nsyl3.mm"
include "wb.mm"
include "cardon.mm"
include "domtriord.mm"
include "mp2an.mm"
include "sylibr.mm"
include "endomtr.mm"
include "syl2anc.mm"
include "impbid1.mm"

theorem alephsucdom
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( B e. On -> ( A ~<_ ( aleph ` B ) <-> A ~< ( aleph ` suc B ) ) )

  proof
    cB
    con0
    wcel
    #
    cA
    cB
    cale
    cfv
    #
    cdom
    wbr
    #
    cA
    cB
    csuc
    #
    cale
    cfv
    #
    csdm
    wbr
    #
    @0
    @1
    @4
    csdm
    wbr
    #
    @2
    @5
    cB
    alephordilem1
    @2
    @6
    @5
    cA
    @1
    @4
    domsdomtr
    ex
    syl5com
    @5
    cA
    cA
    ccrd
    cfv
    #
    cen
    wbr
    @7
    @1
    cdom
    wbr
    #
    @2
    @5
    @7
    cA
    @5
    cA
    @4
    cdom
    wbr
    #
    cA
    ccrd
    cdm
    wcel
    #
    @7
    cA
    cen
    wbr
    #
    cA
    @4
    sdomdom
    @4
    con0
    wcel
    @9
    @10
    @3
    alephon
    @4
    cA
    ondomen
    mpan
    cA
    cardid2
    3syl
    #
    ensymd
    @5
    @1
    @7
    csdm
    wbr
    #
    wn
    #
    @8
    @13
    @7
    @4
    csdm
    wbr
    #
    @5
    @13
    @15
    cB
    @7
    alephnbtwn2
    imnani
    @11
    @5
    @15
    @12
    @7
    cA
    @4
    ensdomtr
    mpancom
    nsyl3
    @7
    con0
    wcel
    @1
    con0
    wcel
    @8
    @14
    wb
    cA
    cardon
    cB
    alephon
    @7
    @1
    domtriord
    mp2an
    sylibr
    cA
    @7
    @1
    endomtr
    syl2anc
    impbid1
end
