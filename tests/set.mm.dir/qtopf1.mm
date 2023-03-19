include "cqtop.mm"
include "co.mm"
include "ccn.mm"
include "wcel.mm"
include "ccnv.mm"
include "chmeo.mm"
include "ctopon.mm"
include "cfv.mm"
include "wfn.mm"
include "wf1.mm"
include "f1fn.mm"
include "syl.mm"
include "qtopid.mm"
include "syl2anc.mm"
include "crn.mm"
include "wf.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "wf1o.mm"
include "f1f1orn.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "4syl.mm"
include "wa.mm"
include "imacnvcnv.mm"
include "wss.mm"
include "imassrn.mm"
include "a1i.mm"
include "wceq.mm"
include "adantr.mm"
include "toponss.mm"
include "sylan.mm"
include "f1imacnv.mm"
include "simpr.mm"
include "eqeltrd.mm"
include "wb.mm"
include "wfo.mm"
include "dffn4.mm"
include "sylib.mm"
include "elqtop3.mm"
include "mpbir2and.mm"
include "syl5eqel.mm"
include "ralrimiva.mm"
include "qtoptopon.mm"
include "iscn.mm"
include "ishmeo.mm"
include "sylanbrc.mm"

theorem qtopf1
  let wph: wff ph
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume qtopf1.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume qtopf1.2: |- ( ph -> F : X -1-1-> Y )


  assert |- ( ph -> F e. ( J Homeo ( J qTop F ) ) )

  proof
    wph
    cF
    cJ
    cJ
    cF
    cqtop
    co
    #
    ccn
    co
    wcel
    #
    cF
    ccnv
    #
    @0
    cJ
    ccn
    co
    wcel
    #
    cF
    cJ
    @0
    chmeo
    co
    wcel
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cF
    cX
    wfn
    #
    @1
    qtopf1.1
    wph
    cX
    cY
    cF
    wf1
    #
    @5
    qtopf1.2
    cX
    cY
    cF
    f1fn
    syl
    #
    cF
    cJ
    cX
    qtopid
    syl2anc
    wph
    @3
    cF
    crn
    #
    cX
    @2
    wf
    #
    @2
    ccnv
    vx
    cv
    #
    cima
    #
    @0
    wcel
    #
    vx
    cJ
    wral
    #
    wph
    @6
    cX
    @8
    cF
    wf1o
    @8
    cX
    @2
    wf1o
    @9
    qtopf1.2
    cX
    cY
    cF
    f1f1orn
    cX
    @8
    cF
    f1ocnv
    @8
    cX
    @2
    f1of
    4syl
    wph
    @12
    vx
    cJ
    wph
    @10
    cJ
    wcel
    #
    wa
    #
    @11
    cF
    @10
    cima
    #
    @0
    cF
    @10
    imacnvcnv
    @15
    @16
    @0
    wcel
    #
    @16
    @8
    wss
    #
    @2
    @16
    cima
    #
    cJ
    wcel
    #
    @18
    @15
    cF
    @10
    imassrn
    a1i
    @15
    @19
    @10
    cJ
    @15
    @6
    @10
    cX
    wss
    #
    @19
    @10
    wceq
    wph
    @6
    @14
    qtopf1.2
    adantr
    wph
    @4
    @14
    @21
    qtopf1.1
    @10
    cJ
    cX
    toponss
    sylan
    cX
    cY
    @10
    cF
    f1imacnv
    syl2anc
    wph
    @14
    simpr
    eqeltrd
    wph
    @17
    @18
    @20
    wa
    wb
    #
    @14
    wph
    @4
    cX
    @8
    cF
    wfo
    #
    @22
    qtopf1.1
    wph
    @5
    @23
    @7
    cX
    cF
    dffn4
    sylib
    #
    @16
    cF
    cJ
    cX
    @8
    elqtop3
    syl2anc
    adantr
    mpbir2and
    syl5eqel
    ralrimiva
    wph
    @0
    @8
    ctopon
    cfv
    wcel
    #
    @4
    @3
    @9
    @13
    wa
    wb
    wph
    @4
    @23
    @25
    qtopf1.1
    @24
    cF
    cJ
    cX
    @8
    qtoptopon
    syl2anc
    qtopf1.1
    vx
    @2
    @0
    cJ
    @8
    cX
    iscn
    syl2anc
    mpbir2and
    cF
    cJ
    @0
    ishmeo
    sylanbrc
end
