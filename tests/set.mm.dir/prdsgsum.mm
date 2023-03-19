include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wfn.mm"
include "wceq.mm"
include "cbs.mm"
include "eqid.mm"
include "ccmn.mm"
include "wf.mm"
include "fmptd.mm"
include "ffn.mm"
include "syl.mm"
include "prdscmnd.mm"
include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "anassrs.mm"
include "an32s.mm"
include "ralrimiva.mm"
include "wb.mm"
include "prdsbasmpt2.mm"
include "adantr.mm"
include "mpbird.mm"
include "gsumcl.mm"
include "prdsbasfn.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfmpt.mm"
include "nfov.mm"
include "dffn5f.mm"
include "sylib.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "cmhm.mm"
include "prdspjmhm.mm"
include "eleqtrd.mm"
include "adantlr.mm"
include "cfsupp.mm"
include "wbr.mm"
include "fveq1.mm"
include "gsummhm2.mm"
include "eqtr3d.mm"
include "eqtr4d.mm"

theorem prdsgsum
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let cJ: class J
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let va: setvar a
  assume prdsgsum.y: |- Y = ( S Xs_ ( x e. I |-> R ) )
  assume prdsgsum.b: |- B = ( Base ` R )
  assume prdsgsum.z: |- .0. = ( 0g ` Y )
  assume prdsgsum.i: |- ( ph -> I e. V )
  assume prdsgsum.j: |- ( ph -> J e. W )
  assume prdsgsum.s: |- ( ph -> S e. X )
  assume prdsgsum.r: |- ( ( ph /\ x e. I ) -> R e. CMnd )
  assume prdsgsum.f: |- ( ( ph /\ ( x e. I /\ y e. J ) ) -> U e. B )
  assume prdsgsum.w: |- ( ph -> ( y e. J |-> ( x e. I |-> U ) ) finSupp .0. )

  disjoint x y
  disjoint I x
  disjoint I y
  disjoint J x
  disjoint J y
  disjoint Y x
  disjoint Y y
  disjoint ph x
  disjoint ph y
  disjoint a x
  disjoint a y
  disjoint I a
  disjoint J a
  disjoint R a
  disjoint U a
  disjoint Y a
  disjoint a ph
  assert |- ( ph -> ( Y gsum ( y e. J |-> ( x e. I |-> U ) ) ) = ( x e. I |-> ( R gsum ( y e. J |-> U ) ) ) )

  proof
    wph
    cY
    vy
    cJ
    vx
    cI
    cU
    cmpt
    #
    cmpt
    #
    cgsu
    co
    #
    vx
    cI
    vx
    cv
    #
    @2
    cfv
    #
    cmpt
    #
    vx
    cI
    cR
    vy
    cJ
    cU
    cmpt
    #
    cgsu
    co
    #
    cmpt
    wph
    @2
    cI
    wfn
    @2
    @5
    wceq
    wph
    cY
    cbs
    cfv
    #
    vx
    cI
    cR
    cmpt
    #
    cS
    @2
    cI
    cX
    cV
    cY
    prdsgsum.y
    @8
    eqid
    #
    prdsgsum.s
    prdsgsum.i
    wph
    cI
    ccmn
    @9
    wf
    @9
    cI
    wfn
    wph
    vx
    cI
    cR
    ccmn
    @9
    prdsgsum.r
    @9
    eqid
    #
    fmptd
    #
    cI
    ccmn
    @9
    ffn
    syl
    wph
    cJ
    @8
    @1
    cY
    cW
    c.0
    @10
    prdsgsum.z
    wph
    @9
    cS
    cI
    cX
    cV
    cY
    prdsgsum.y
    prdsgsum.i
    prdsgsum.s
    @12
    prdscmnd
    #
    prdsgsum.j
    wph
    vy
    cJ
    @0
    @8
    @1
    wph
    vy
    cv
    cJ
    wcel
    #
    wa
    #
    @0
    @8
    wcel
    #
    cU
    cB
    wcel
    #
    vx
    cI
    wral
    #
    @15
    @17
    vx
    cI
    wph
    @3
    cI
    wcel
    #
    @14
    @17
    wph
    @19
    @14
    @17
    prdsgsum.f
    anassrs
    #
    an32s
    ralrimiva
    wph
    @16
    @18
    wb
    @14
    wph
    vx
    @8
    cR
    cS
    cU
    cI
    cB
    cX
    cV
    ccmn
    cY
    prdsgsum.y
    @10
    prdsgsum.s
    prdsgsum.i
    wph
    cR
    ccmn
    wcel
    #
    vx
    cI
    prdsgsum.r
    ralrimiva
    prdsgsum.b
    prdsbasmpt2
    adantr
    mpbird
    #
    @1
    eqid
    fmptd
    prdsgsum.w
    gsumcl
    prdsbasfn
    vx
    cI
    @2
    vx
    cY
    @1
    cgsu
    vx
    cY
    nfcv
    vx
    cgsu
    nfcv
    vx
    vy
    cJ
    @0
    vx
    cJ
    nfcv
    vx
    cI
    cU
    nfmpt1
    nfmpt
    nfov
    dffn5f
    sylib
    wph
    vx
    cI
    @7
    @4
    wph
    @19
    wa
    #
    cR
    vy
    cJ
    @3
    @0
    cfv
    #
    cmpt
    #
    cgsu
    co
    @7
    @4
    @23
    @25
    @6
    cR
    cgsu
    @23
    vy
    cJ
    @24
    cU
    @23
    @14
    wa
    @19
    @17
    @24
    cU
    wceq
    @23
    @19
    @14
    wph
    @19
    simpr
    #
    adantr
    @20
    vx
    cI
    cU
    cB
    @0
    @0
    eqid
    fvmpt2
    syl2anc
    mpteq2dva
    oveq2d
    @23
    va
    cJ
    @8
    @3
    va
    cv
    #
    cfv
    #
    @24
    vy
    @4
    cY
    cR
    cW
    @0
    c.0
    @10
    prdsgsum.z
    wph
    cY
    ccmn
    wcel
    @19
    @13
    adantr
    @23
    @21
    cR
    cmnd
    wcel
    prdsgsum.r
    cR
    cmnmnd
    syl
    #
    wph
    cJ
    cW
    wcel
    @19
    prdsgsum.j
    adantr
    @23
    va
    @8
    @28
    cmpt
    cY
    @3
    @9
    cfv
    #
    cmhm
    co
    cY
    cR
    cmhm
    co
    @23
    va
    @3
    @8
    @9
    cS
    cI
    cV
    cX
    cY
    prdsgsum.y
    @10
    wph
    cI
    cV
    wcel
    @19
    prdsgsum.i
    adantr
    wph
    cS
    cX
    wcel
    @19
    prdsgsum.s
    adantr
    wph
    cI
    cmnd
    @9
    wf
    @19
    wph
    vx
    cI
    cR
    cmnd
    @9
    @29
    @11
    fmptd
    adantr
    @26
    prdspjmhm
    @23
    @30
    cR
    cY
    cmhm
    @23
    @19
    @21
    @30
    cR
    wceq
    @26
    prdsgsum.r
    vx
    cI
    cR
    ccmn
    @9
    @11
    fvmpt2
    syl2anc
    oveq2d
    eleqtrd
    wph
    @14
    @16
    @19
    @22
    adantlr
    wph
    @1
    c.0
    cfsupp
    wbr
    @19
    prdsgsum.w
    adantr
    @3
    @27
    @0
    fveq1
    @3
    @27
    @2
    fveq1
    gsummhm2
    eqtr3d
    mpteq2dva
    eqtr4d
end
