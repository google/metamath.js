include "wcel.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cun.mm"
include "cvv.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "wa.mm"
include "cab.mm"
include "trclexlem.mm"
include "ssun1.mm"
include "wbr.mm"
include "wex.mm"
include "copab.mm"
include "ccnv.mm"
include "wceq.mm"
include "wrel.mm"
include "relcnv.mm"
include "relssdmrn.mm"
include "ax-mp.mm"
include "ssequn1.mm"
include "mpbi.mm"
include "cnvun.mm"
include "cnvxp.mm"
include "df-rn.mm"
include "dfdm4.mm"
include "xpeq12i.mm"
include "eqtri.mm"
include "uneq2i.mm"
include "3eqtr4i.mm"
include "breqi.mm"
include "vex.mm"
include "brcnv.mm"
include "3bitr3i.mm"
include "anbi12i.mm"
include "biimpi.mm"
include "eximi.mm"
include "ssopab2i.mm"
include "df-co.mm"
include "3sstr4i.mm"
include "xptrrel.mm"
include "ssun2.mm"
include "sstri.mm"
include "trcleq2lem.mm"
include "elabg.mm"
include "biimprd.mm"
include "mp2ani.mm"
include "syl.mm"

theorem trclublem
  let vx: setvar x
  let cR: class R
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c

  disjoint R x
  disjoint a b
  disjoint a c
  disjoint R a
  disjoint b c
  disjoint R b
  disjoint R c
  assert |- ( R e. V -> ( R u. ( dom R X. ran R ) ) e. { x | ( R C_ x /\ ( x o. x ) C_ x ) } )

  proof
    cR
    cV
    wcel
    cR
    cR
    cdm
    #
    cR
    crn
    #
    cxp
    #
    cun
    #
    cvv
    wcel
    #
    @3
    cR
    vx
    cv
    #
    wss
    @5
    @5
    ccom
    @5
    wss
    wa
    #
    vx
    cab
    wcel
    #
    cR
    cV
    trclexlem
    @4
    cR
    @3
    wss
    #
    @3
    @3
    ccom
    #
    @3
    wss
    #
    @7
    cR
    @2
    ssun1
    @9
    @2
    @2
    ccom
    #
    @3
    va
    cv
    #
    vb
    cv
    #
    @3
    wbr
    #
    @13
    vc
    cv
    #
    @3
    wbr
    #
    wa
    #
    vb
    wex
    #
    va
    vc
    copab
    @12
    @13
    @2
    wbr
    #
    @13
    @15
    @2
    wbr
    #
    wa
    #
    vb
    wex
    #
    va
    vc
    copab
    @9
    @11
    @18
    @22
    va
    vc
    @17
    @21
    vb
    @17
    @21
    @14
    @19
    @16
    @20
    @13
    @12
    @3
    ccnv
    #
    wbr
    @13
    @12
    @2
    ccnv
    #
    wbr
    @14
    @19
    @13
    @12
    @23
    @24
    cR
    ccnv
    #
    @25
    cdm
    #
    @25
    crn
    #
    cxp
    #
    cun
    #
    @28
    @23
    @24
    @25
    @28
    wss
    #
    @29
    @28
    wceq
    @25
    wrel
    @30
    cR
    relcnv
    @25
    relssdmrn
    ax-mp
    @25
    @28
    ssequn1
    mpbi
    @23
    @25
    @24
    cun
    @29
    cR
    @2
    cnvun
    @24
    @28
    @25
    @24
    @1
    @0
    cxp
    @28
    @0
    @1
    cnvxp
    @1
    @26
    @0
    @27
    cR
    df-rn
    cR
    dfdm4
    xpeq12i
    eqtri
    #
    uneq2i
    eqtri
    @31
    3eqtr4i
    #
    breqi
    @13
    @12
    @3
    vb
    vex
    #
    va
    vex
    #
    brcnv
    @13
    @12
    @2
    @33
    @34
    brcnv
    3bitr3i
    @15
    @13
    @23
    wbr
    @15
    @13
    @24
    wbr
    @16
    @20
    @15
    @13
    @23
    @24
    @32
    breqi
    @15
    @13
    @3
    vc
    vex
    #
    @33
    brcnv
    @15
    @13
    @2
    @35
    @33
    brcnv
    3bitr3i
    anbi12i
    biimpi
    eximi
    ssopab2i
    va
    vc
    vb
    @3
    @3
    df-co
    va
    vc
    vb
    @2
    @2
    df-co
    3sstr4i
    @11
    @2
    @3
    @0
    @1
    xptrrel
    @2
    cR
    ssun2
    sstri
    sstri
    @4
    @7
    @8
    @10
    wa
    #
    @6
    @36
    vx
    @3
    cvv
    @5
    @3
    cR
    trcleq2lem
    elabg
    biimprd
    mp2ani
    syl
end
