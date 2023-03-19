include "cts.mm"
include "cfv.mm"
include "cbs.mm"
include "ctopon.mm"
include "wcel.mm"
include "ctps.mm"
include "cv.mm"
include "ctopn.mm"
include "cmpt.mm"
include "cpt.mm"
include "cixp.mm"
include "wral.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "eqid.mm"
include "istps.mm"
include "sylib.mm"
include "ralrimiva.mm"
include "pttopon.mm"
include "syl2anc.mm"
include "ccom.mm"
include "cvv.mm"
include "wf.mm"
include "fex.mm"
include "cdm.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "prdstset.mm"
include "wfn.mm"
include "topnfn.mm"
include "dffn2.mm"
include "mpbi.mm"
include "wss.mm"
include "ssv.mm"
include "fss.mm"
include "sylancl.mm"
include "fcompt.mm"
include "sylancr.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "prdsbas.mm"
include "3eltr4d.mm"
include "tsettps.mm"

theorem prdstps
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume prdstopn.y: |- Y = ( S Xs_ R )
  assume prdstopn.s: |- ( ph -> S e. V )
  assume prdstopn.i: |- ( ph -> I e. W )
  assume prdstps.r: |- ( ph -> R : I --> TopSp )


  assert |- ( ph -> Y e. TopSp )

  proof
    wph
    cY
    cts
    cfv
    #
    cY
    cbs
    cfv
    #
    ctopon
    cfv
    #
    wcel
    cY
    ctps
    wcel
    wph
    vx
    cI
    vx
    cv
    #
    cR
    cfv
    #
    ctopn
    cfv
    #
    cmpt
    #
    cpt
    cfv
    #
    vx
    cI
    @4
    cbs
    cfv
    #
    cixp
    #
    ctopon
    cfv
    #
    @0
    @2
    wph
    cI
    cW
    wcel
    #
    @5
    @8
    ctopon
    cfv
    wcel
    #
    vx
    cI
    wral
    @7
    @10
    wcel
    prdstopn.i
    wph
    @12
    vx
    cI
    wph
    @3
    cI
    wcel
    wa
    @4
    ctps
    wcel
    @12
    wph
    cI
    ctps
    @3
    cR
    prdstps.r
    ffvelrnda
    @8
    @5
    @4
    @8
    eqid
    @5
    eqid
    istps
    sylib
    ralrimiva
    vx
    cI
    @8
    @7
    @5
    cW
    @7
    eqid
    pttopon
    syl2anc
    wph
    @0
    ctopn
    cR
    ccom
    #
    cpt
    cfv
    @7
    wph
    @1
    cY
    cR
    cS
    cI
    @0
    cV
    cvv
    prdstopn.y
    prdstopn.s
    wph
    cI
    ctps
    cR
    wf
    #
    @11
    cR
    cvv
    wcel
    prdstps.r
    prdstopn.i
    cI
    ctps
    cW
    cR
    fex
    syl2anc
    #
    @1
    eqid
    #
    wph
    @14
    cR
    cdm
    cI
    wceq
    prdstps.r
    cI
    ctps
    cR
    fdm
    syl
    #
    @0
    eqid
    #
    prdstset
    wph
    @13
    @6
    cpt
    wph
    cvv
    cvv
    ctopn
    wf
    #
    cI
    cvv
    cR
    wf
    #
    @13
    @6
    wceq
    ctopn
    cvv
    wfn
    @19
    topnfn
    cvv
    ctopn
    dffn2
    mpbi
    wph
    @14
    ctps
    cvv
    wss
    @20
    prdstps.r
    ctps
    ssv
    cI
    ctps
    cvv
    cR
    fss
    sylancl
    vx
    ctopn
    cR
    cI
    cvv
    cvv
    fcompt
    sylancr
    fveq2d
    eqtrd
    wph
    @1
    @9
    ctopon
    wph
    vx
    @1
    cY
    cR
    cS
    cI
    cV
    cvv
    prdstopn.y
    prdstopn.s
    @15
    @16
    @17
    prdsbas
    fveq2d
    3eltr4d
    @1
    @0
    cY
    @16
    @18
    tsettps
    syl
end
