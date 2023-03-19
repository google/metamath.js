include "wss.mm"
include "ccom.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cun.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "xptrrel.mm"
include "ssun2.mm"
include "sstri.mm"
include "a1i.mm"
include "coeq12d.mm"
include "coundir.mm"
include "ccnv.mm"
include "wrel.mm"
include "wceq.mm"
include "relcnv.mm"
include "cocnvcnv1.mm"
include "relssdmrn.mm"
include "dmcnvcnv.mm"
include "rncnvcnv.mm"
include "xpeq12i.mm"
include "syl6sseq.mm"
include "coss1.mm"
include "syl.mm"
include "syl5eqssr.mm"
include "ssequn1.mm"
include "sylib.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "coundi.mm"
include "cocnvcnv2.mm"
include "coss2.mm"
include "syl6eq.mm"
include "3sstr4d.mm"
include "jca.mm"

theorem trrelsuperrel2dg
  let wph: wff ph
  let cR: class R
  let cS: class S
  assume trrelsuperrel2dg.s: |- ( ph -> S = ( R u. ( dom R X. ran R ) ) )


  assert |- ( ph -> ( R C_ S /\ ( S o. S ) C_ S ) )

  proof
    wph
    cR
    cS
    wss
    cS
    cS
    ccom
    #
    cS
    wss
    wph
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
    cR
    cS
    cR
    @3
    ssun1
    trrelsuperrel2dg.s
    syl5sseqr
    wph
    @3
    @3
    ccom
    #
    @4
    @0
    cS
    @5
    @4
    wss
    wph
    @5
    @3
    @4
    @1
    @2
    xptrrel
    @3
    cR
    ssun2
    sstri
    a1i
    wph
    @0
    @4
    @4
    ccom
    #
    @5
    wph
    cS
    @4
    cS
    @4
    trrelsuperrel2dg.s
    trrelsuperrel2dg.s
    coeq12d
    @6
    @3
    @4
    ccom
    #
    @5
    @6
    cR
    @4
    ccom
    #
    @7
    cun
    #
    @7
    cR
    @3
    @4
    coundir
    cR
    ccnv
    #
    ccnv
    #
    wrel
    #
    @9
    @7
    wceq
    #
    @10
    relcnv
    #
    @12
    @8
    @7
    wss
    @13
    @12
    @8
    @11
    @4
    ccom
    #
    @7
    cR
    @4
    cocnvcnv1
    @12
    @11
    @3
    wss
    #
    @15
    @7
    wss
    @12
    @11
    @11
    cdm
    #
    @11
    crn
    #
    cxp
    @3
    @11
    relssdmrn
    @17
    @1
    @18
    @2
    cR
    dmcnvcnv
    cR
    rncnvcnv
    xpeq12i
    syl6sseq
    #
    @11
    @3
    @4
    coss1
    syl
    syl5eqssr
    @8
    @7
    ssequn1
    sylib
    ax-mp
    eqtri
    @7
    @3
    cR
    ccom
    #
    @5
    cun
    #
    @5
    @3
    cR
    @3
    coundi
    @12
    @21
    @5
    wceq
    #
    @14
    @12
    @20
    @5
    wss
    @22
    @12
    @20
    @3
    @11
    ccom
    #
    @5
    @3
    cR
    cocnvcnv2
    @12
    @16
    @23
    @5
    wss
    @19
    @11
    @3
    @3
    coss2
    syl
    syl5eqssr
    @20
    @5
    ssequn1
    sylib
    ax-mp
    eqtri
    eqtri
    syl6eq
    trrelsuperrel2dg.s
    3sstr4d
    jca
end
