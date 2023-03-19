include "char.mm"
include "cfv.mm"
include "cpw.mm"
include "cen.mm"
include "wbr.mm"
include "cgch.mm"
include "wcel.mm"
include "cfn.mm"
include "cv.mm"
include "csdm.mm"
include "wa.mm"
include "wn.mm"
include "wal.mm"
include "wo.mm"
include "wi.mm"
include "cdom.mm"
include "ccrd.mm"
include "cdm.mm"
include "wb.mm"
include "con0.mm"
include "harcl.mm"
include "sdomdom.mm"
include "ondomen.mm"
include "sylancr.mm"
include "onenon.mm"
include "ax-mp.mm"
include "cardsdom2.mm"
include "sylancl.mm"
include "ibir.mm"
include "harcard.mm"
include "syl6eleq.mm"
include "elharval.mm"
include "simprbi.mm"
include "syl.mm"
include "cardid2.mm"
include "domen1.mm"
include "3syl.mm"
include "mpbid.mm"
include "domnsym.mm"
include "con2i.mm"
include "sdomen2.mm"
include "notbid.mm"
include "syl5ib.mm"
include "imnan.mm"
include "sylib.mm"
include "alrimiv.mm"
include "olcd.mm"
include "cvv.mm"
include "relen.mm"
include "brrelex2i.mm"
include "pwexb.mm"
include "sylibr.mm"
include "elgch.mm"
include "mpbird.mm"

theorem hargch
  let cA: class A
  let vx: setvar x


  assert |- ( ( har ` A ) ~~ ~P A -> A e. GCH )

  proof
    cA
    char
    cfv
    #
    cA
    cpw
    #
    cen
    wbr
    #
    cA
    cgch
    wcel
    #
    cA
    cfn
    wcel
    #
    cA
    vx
    cv
    #
    csdm
    wbr
    #
    @5
    @1
    csdm
    wbr
    #
    wa
    wn
    #
    vx
    wal
    #
    wo
    #
    @2
    @9
    @4
    @2
    @8
    vx
    @2
    @6
    @7
    wn
    #
    wi
    @8
    @6
    @5
    @0
    csdm
    wbr
    #
    wn
    @2
    @11
    @12
    @6
    @12
    @5
    cA
    cdom
    wbr
    #
    @6
    wn
    @12
    @5
    ccrd
    cfv
    #
    cA
    cdom
    wbr
    #
    @13
    @12
    @14
    @0
    wcel
    #
    @15
    @12
    @14
    @0
    ccrd
    cfv
    #
    @0
    @12
    @14
    @17
    wcel
    #
    @12
    @5
    ccrd
    cdm
    #
    wcel
    #
    @0
    @19
    wcel
    #
    @18
    @12
    wb
    @12
    @0
    con0
    wcel
    #
    @5
    @0
    cdom
    wbr
    @20
    cA
    harcl
    #
    @5
    @0
    sdomdom
    @0
    @5
    ondomen
    sylancr
    #
    @22
    @21
    @23
    @0
    onenon
    ax-mp
    @5
    @0
    cardsdom2
    sylancl
    ibir
    cA
    harcard
    syl6eleq
    @16
    @14
    con0
    wcel
    @15
    cA
    @14
    elharval
    simprbi
    syl
    @12
    @20
    @14
    @5
    cen
    wbr
    @15
    @13
    wb
    @24
    @5
    cardid2
    @14
    @5
    cA
    domen1
    3syl
    mpbid
    @5
    cA
    domnsym
    syl
    con2i
    @2
    @12
    @7
    @0
    @1
    @5
    sdomen2
    notbid
    syl5ib
    @6
    @7
    imnan
    sylib
    alrimiv
    olcd
    @2
    cA
    cvv
    wcel
    #
    @3
    @10
    wb
    @2
    @1
    cvv
    wcel
    @25
    @0
    @1
    cen
    relen
    brrelex2i
    cA
    pwexb
    sylibr
    vx
    cA
    cvv
    elgch
    syl
    mpbird
end
