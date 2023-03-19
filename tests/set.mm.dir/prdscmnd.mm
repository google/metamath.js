include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "eqidd.mm"
include "ccmn.mm"
include "wf.mm"
include "cmnd.mm"
include "wss.mm"
include "cv.mm"
include "cmnmnd.mm"
include "ssriv.mm"
include "fss.mm"
include "sylancl.mm"
include "prdsmndd.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cmpt.mm"
include "wa.mm"
include "wceq.mm"
include "3ad2ant1.mm"
include "ffvelrnda.mm"
include "cvv.mm"
include "eqid.mm"
include "elex.mm"
include "syl.mm"
include "adantr.mm"
include "wfn.mm"
include "ffn.mm"
include "simpl2.mm"
include "simpr.mm"
include "prdsbasprj.mm"
include "simpl3.mm"
include "cmncom.mm"
include "syl3anc.mm"
include "mpteq2dva.mm"
include "simp2.mm"
include "simp3.mm"
include "prdsplusgval.mm"
include "3eqtr4d.mm"
include "iscmnd.mm"

theorem prdscmnd
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vc: setvar c
  let va: setvar a
  let vb: setvar b
  assume prdscmnd.y: |- Y = ( S Xs_ R )
  assume prdscmnd.i: |- ( ph -> I e. W )
  assume prdscmnd.s: |- ( ph -> S e. V )
  assume prdscmnd.r: |- ( ph -> R : I --> CMnd )


  assert |- ( ph -> Y e. CMnd )

  proof
    wph
    va
    vb
    cY
    cbs
    cfv
    #
    cY
    cplusg
    cfv
    #
    cY
    wph
    @0
    eqidd
    wph
    @1
    eqidd
    wph
    cR
    cS
    cI
    cV
    cW
    cY
    prdscmnd.y
    prdscmnd.i
    prdscmnd.s
    wph
    cI
    ccmn
    cR
    wf
    #
    ccmn
    cmnd
    wss
    cI
    cmnd
    cR
    wf
    prdscmnd.r
    va
    ccmn
    cmnd
    va
    cv
    #
    cmnmnd
    ssriv
    cI
    ccmn
    cmnd
    cR
    fss
    sylancl
    prdsmndd
    wph
    @3
    @0
    wcel
    #
    vb
    cv
    #
    @0
    wcel
    #
    w3a
    #
    vc
    cI
    vc
    cv
    #
    @3
    cfv
    #
    @8
    @5
    cfv
    #
    @8
    cR
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cmpt
    vc
    cI
    @10
    @9
    @12
    co
    #
    cmpt
    @3
    @5
    @1
    co
    @5
    @3
    @1
    co
    @7
    vc
    cI
    @13
    @14
    @7
    @8
    cI
    wcel
    #
    wa
    #
    @11
    ccmn
    wcel
    @9
    @11
    cbs
    cfv
    #
    wcel
    @10
    @17
    wcel
    @13
    @14
    wceq
    @7
    cI
    ccmn
    @8
    cR
    wph
    @4
    @2
    @6
    prdscmnd.r
    3ad2ant1
    ffvelrnda
    @16
    @0
    cR
    cS
    @3
    cI
    @8
    cvv
    cvv
    cY
    prdscmnd.y
    @0
    eqid
    #
    @7
    cS
    cvv
    wcel
    #
    @15
    wph
    @4
    @19
    @6
    wph
    cS
    cV
    wcel
    @19
    prdscmnd.s
    cS
    cV
    elex
    syl
    3ad2ant1
    #
    adantr
    #
    @7
    cI
    cvv
    wcel
    #
    @15
    wph
    @4
    @22
    @6
    wph
    cI
    cW
    wcel
    @22
    prdscmnd.i
    cI
    cW
    elex
    syl
    3ad2ant1
    #
    adantr
    #
    @7
    cR
    cI
    wfn
    #
    @15
    wph
    @4
    @25
    @6
    wph
    @2
    @25
    prdscmnd.r
    cI
    ccmn
    cR
    ffn
    syl
    3ad2ant1
    #
    adantr
    #
    wph
    @4
    @6
    @15
    simpl2
    @7
    @15
    simpr
    #
    prdsbasprj
    @16
    @0
    cR
    cS
    @5
    cI
    @8
    cvv
    cvv
    cY
    prdscmnd.y
    @18
    @21
    @24
    @27
    wph
    @4
    @6
    @15
    simpl3
    @28
    prdsbasprj
    @17
    @12
    @11
    @9
    @10
    @17
    eqid
    @12
    eqid
    cmncom
    syl3anc
    mpteq2dva
    @7
    vc
    @0
    @1
    cR
    cS
    @3
    @5
    cI
    cvv
    cvv
    cY
    prdscmnd.y
    @18
    @20
    @23
    @26
    wph
    @4
    @6
    simp2
    #
    wph
    @4
    @6
    simp3
    #
    @1
    eqid
    #
    prdsplusgval
    @7
    vc
    @0
    @1
    cR
    cS
    @5
    @3
    cI
    cvv
    cvv
    cY
    prdscmnd.y
    @18
    @20
    @23
    @26
    @30
    @29
    @31
    prdsplusgval
    3eqtr4d
    iscmnd
end
