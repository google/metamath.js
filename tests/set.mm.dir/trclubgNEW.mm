include "cv.mm"
include "ccom.mm"
include "wss.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cun.mm"
include "cvv.mm"
include "wcel.mm"
include "dmexg.mm"
include "syl.mm"
include "rnexg.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "unexg.mm"
include "wceq.mm"
include "id.mm"
include "coeq12d.mm"
include "sseq12d.mm"
include "ssun1.mm"
include "a1i.mm"
include "ccnv.mm"
include "cnvssrndm.mm"
include "coundi.mm"
include "cnvss.mm"
include "coss2.mm"
include "cocnvcnv2.mm"
include "cnvxp.mm"
include "coeq2i.mm"
include "3sstr3g.mm"
include "ssequn1.mm"
include "sylib.mm"
include "coundir.mm"
include "coss1.mm"
include "cocnvcnv1.mm"
include "coeq1i.mm"
include "xptrrel.mm"
include "ssun2.mm"
include "sstri.mm"
include "eqsstrd.mm"
include "syl5eqss.mm"
include "mp1i.mm"
include "clublem.mm"

theorem trclubgNEW
  let wph: wff ph
  let vx: setvar x
  let cR: class R
  assume trclubgNEW.rex: |- ( ph -> R e. _V )

  disjoint R x
  assert |- ( ph -> |^| { x | ( R C_ x /\ ( x o. x ) C_ x ) } C_ ( R u. ( dom R X. ran R ) ) )

  proof
    wph
    vx
    cv
    #
    @0
    ccom
    #
    @0
    wss
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
    @5
    ccom
    #
    @5
    wss
    #
    vx
    cR
    @5
    wph
    cR
    cvv
    wcel
    #
    @4
    cvv
    wcel
    #
    @5
    cvv
    wcel
    trclubgNEW.rex
    wph
    @2
    cvv
    wcel
    #
    @3
    cvv
    wcel
    #
    @9
    wph
    @8
    @10
    trclubgNEW.rex
    cR
    cvv
    dmexg
    syl
    wph
    @8
    @11
    trclubgNEW.rex
    cR
    cvv
    rnexg
    syl
    @2
    @3
    cvv
    cvv
    xpexg
    syl2anc
    cR
    @4
    cvv
    cvv
    unexg
    syl2anc
    @0
    @5
    wceq
    #
    @1
    @6
    @0
    @5
    @12
    @0
    @5
    @0
    @5
    @12
    id
    #
    @13
    coeq12d
    @13
    sseq12d
    cR
    @5
    wss
    wph
    cR
    @4
    ssun1
    a1i
    cR
    ccnv
    #
    @3
    @2
    cxp
    #
    wss
    #
    @7
    wph
    cR
    cnvssrndm
    @16
    @6
    @5
    cR
    ccom
    #
    @5
    @4
    ccom
    #
    cun
    #
    @5
    @5
    cR
    @4
    coundi
    @16
    @19
    @18
    @5
    @16
    @17
    @18
    wss
    @19
    @18
    wceq
    @16
    @5
    @14
    ccnv
    #
    ccom
    #
    @5
    @15
    ccnv
    #
    ccom
    #
    @17
    @18
    @16
    @20
    @22
    wss
    #
    @21
    @23
    wss
    @14
    @15
    cnvss
    #
    @20
    @22
    @5
    coss2
    syl
    @5
    cR
    cocnvcnv2
    @22
    @4
    @5
    @3
    @2
    cnvxp
    #
    coeq2i
    3sstr3g
    @17
    @18
    ssequn1
    sylib
    @16
    @18
    cR
    @4
    ccom
    #
    @4
    @4
    ccom
    #
    cun
    #
    @5
    cR
    @4
    @4
    coundir
    @16
    @29
    @28
    @5
    @16
    @27
    @28
    wss
    @29
    @28
    wceq
    @16
    @20
    @4
    ccom
    #
    @22
    @4
    ccom
    #
    @27
    @28
    @16
    @24
    @30
    @31
    wss
    @25
    @20
    @22
    @4
    coss1
    syl
    cR
    @4
    cocnvcnv1
    @22
    @4
    @4
    @26
    coeq1i
    3sstr3g
    @27
    @28
    ssequn1
    sylib
    @28
    @5
    wss
    @16
    @28
    @4
    @5
    @2
    @3
    xptrrel
    @4
    cR
    ssun2
    sstri
    a1i
    eqsstrd
    syl5eqss
    eqsstrd
    syl5eqss
    mp1i
    clublem
end
