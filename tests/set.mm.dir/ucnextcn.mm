include "wf.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cucn.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cust.mm"
include "wb.mm"
include "cusp.mm"
include "wss.mm"
include "ressust.mm"
include "syl2anc.mm"
include "cutop.mm"
include "wceq.mm"
include "ccusp.mm"
include "cuspusp.mm"
include "syl.mm"
include "isusp.mm"
include "sylib.mm"
include "simpld.mm"
include "isucn.mm"
include "mpbid.mm"
include "csn.mm"
include "cnei.mm"
include "crest.mm"
include "cfm.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "cfg.mm"
include "ccfilu.mm"
include "cvv.mm"
include "cfbas.mm"
include "adantr.mm"
include "elfvexd.mm"
include "cfil.mm"
include "ccl.mm"
include "simpr.mm"
include "eleqtrrd.mm"
include "ctopon.mm"
include "ctps.mm"
include "istps.mm"
include "trnei.mm"
include "syl3anc.mm"
include "filfbas.mm"
include "fmval.mm"
include "cxp.mm"
include "c0.mm"
include "wn.mm"
include "neipcfilu.mm"
include "0nelfb.mm"
include "trcfilu.mm"
include "syl121anc.mm"
include "cress.mm"
include "cuss.mm"
include "ressuss.mm"
include "oveq1i.mm"
include "3eqtr4g.mm"
include "fveq2d.mm"
include "imaeq2.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "fmucnd.mm"
include "cfilufg.mm"
include "eqeltrd.mm"
include "cnextucn.mm"

theorem ucnextcn
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cJ: class J
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ucnextcn.x: |- X = ( Base ` V )
  assume ucnextcn.y: |- Y = ( Base ` W )
  assume ucnextcn.j: |- J = ( TopOpen ` V )
  assume ucnextcn.k: |- K = ( TopOpen ` W )
  assume ucnextcn.s: |- S = ( UnifSt ` V )
  assume ucnextcn.t: |- T = ( UnifSt ` ( V |`s A ) )
  assume ucnextcn.u: |- U = ( UnifSt ` W )
  assume ucnextcn.v: |- ( ph -> V e. TopSp )
  assume ucnextcn.r: |- ( ph -> V e. UnifSp )
  assume ucnextcn.w: |- ( ph -> W e. TopSp )
  assume ucnextcn.z: |- ( ph -> W e. CUnifSp )
  assume ucnextcn.h: |- ( ph -> K e. Haus )
  assume ucnextcn.a: |- ( ph -> A C_ X )
  assume ucnextcn.f: |- ( ph -> F e. ( T uCn U ) )
  assume ucnextcn.c: |- ( ph -> ( ( cls ` J ) ` A ) = X )


  assert |- ( ph -> ( ( J CnExt K ) ` F ) e. ( J Cn K ) )

  proof
    wph
    vx
    cA
    cU
    cF
    cJ
    cK
    cV
    cW
    cX
    cY
    ucnextcn.x
    ucnextcn.y
    ucnextcn.j
    ucnextcn.k
    ucnextcn.u
    ucnextcn.v
    ucnextcn.w
    ucnextcn.z
    ucnextcn.h
    ucnextcn.a
    wph
    cA
    cY
    cF
    wf
    #
    vy
    cv
    #
    vz
    cv
    #
    vv
    cv
    wbr
    @1
    cF
    cfv
    @2
    cF
    cfv
    vw
    cv
    wbr
    wi
    vz
    cA
    wral
    vy
    cA
    wral
    vv
    cT
    wrex
    vw
    cU
    wral
    #
    wph
    cF
    cT
    cU
    cucn
    co
    wcel
    #
    @0
    @3
    wa
    #
    ucnextcn.f
    wph
    cT
    cA
    cust
    cfv
    wcel
    #
    cU
    cY
    cust
    cfv
    wcel
    #
    @4
    @5
    wb
    wph
    cV
    cusp
    wcel
    #
    cA
    cX
    wss
    #
    @6
    ucnextcn.r
    ucnextcn.a
    cA
    cT
    cV
    cX
    ucnextcn.x
    ucnextcn.t
    ressust
    syl2anc
    #
    wph
    @7
    cK
    cU
    cutop
    cfv
    wceq
    #
    wph
    cW
    cusp
    wcel
    #
    @7
    @11
    wa
    wph
    cW
    ccusp
    wcel
    @12
    ucnextcn.z
    cW
    cuspusp
    syl
    cY
    cU
    cK
    cW
    ucnextcn.y
    ucnextcn.u
    ucnextcn.k
    isusp
    sylib
    simpld
    #
    vy
    vz
    cT
    cF
    cU
    cA
    cY
    vw
    vv
    isucn
    syl2anc
    mpbid
    simpld
    #
    ucnextcn.c
    wph
    vx
    cv
    #
    cX
    wcel
    #
    wa
    #
    @15
    csn
    cJ
    cnei
    cfv
    cfv
    #
    cA
    crest
    co
    #
    cY
    cF
    cfm
    co
    cfv
    #
    cY
    va
    @19
    cF
    va
    cv
    #
    cima
    #
    cmpt
    #
    crn
    #
    cfg
    co
    #
    cU
    ccfilu
    cfv
    #
    @17
    cY
    cvv
    wcel
    @19
    cA
    cfbas
    cfv
    wcel
    #
    @0
    @20
    @25
    wceq
    @17
    cU
    cust
    cY
    wph
    @7
    @16
    @13
    adantr
    #
    elfvexd
    @17
    @19
    cA
    cfil
    cfv
    wcel
    #
    @27
    @17
    @15
    cA
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    @29
    @17
    @15
    cX
    @30
    wph
    @16
    simpr
    #
    wph
    @30
    cX
    wceq
    @16
    ucnextcn.c
    adantr
    eleqtrrd
    @17
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @9
    @16
    @31
    @29
    wb
    wph
    @33
    @16
    wph
    cV
    ctps
    wcel
    #
    @33
    ucnextcn.v
    cX
    cJ
    cV
    ucnextcn.x
    ucnextcn.j
    istps
    sylib
    adantr
    wph
    @9
    @16
    ucnextcn.a
    adantr
    #
    @32
    cA
    @15
    cJ
    cX
    trnei
    syl3anc
    mpbid
    @19
    cA
    filfbas
    syl
    #
    wph
    @0
    @16
    @14
    adantr
    va
    cvv
    @19
    cF
    cY
    cA
    fmval
    syl3anc
    @17
    @7
    @24
    @26
    wcel
    @25
    @26
    wcel
    @28
    @17
    @19
    @24
    cT
    cF
    cU
    cA
    cY
    vb
    wph
    @6
    @16
    @10
    adantr
    #
    @28
    wph
    @4
    @16
    ucnextcn.f
    adantr
    @17
    @19
    cS
    cA
    cA
    cxp
    #
    crest
    co
    #
    ccfilu
    cfv
    #
    cT
    ccfilu
    cfv
    #
    @17
    cS
    cX
    cust
    cfv
    wcel
    #
    @18
    cS
    ccfilu
    cfv
    wcel
    #
    c0
    @19
    wcel
    wn
    #
    @9
    @19
    @40
    wcel
    wph
    @42
    @16
    wph
    @42
    cJ
    cS
    cutop
    cfv
    wceq
    #
    wph
    @8
    @42
    @45
    wa
    ucnextcn.r
    cX
    cS
    cJ
    cV
    ucnextcn.x
    ucnextcn.s
    ucnextcn.j
    isusp
    sylib
    simpld
    adantr
    @17
    @8
    @34
    @16
    @43
    wph
    @8
    @16
    ucnextcn.r
    adantr
    wph
    @34
    @16
    ucnextcn.v
    adantr
    @32
    @15
    cS
    cJ
    cV
    cX
    ucnextcn.x
    ucnextcn.j
    ucnextcn.s
    neipcfilu
    syl3anc
    @17
    @27
    @44
    @36
    cA
    @19
    0nelfb
    syl
    @35
    cA
    cS
    @18
    cX
    trcfilu
    syl121anc
    @17
    cA
    cvv
    wcel
    #
    @41
    @40
    wceq
    @17
    cT
    cust
    cA
    @37
    elfvexd
    @46
    cT
    @39
    ccfilu
    @46
    cV
    cA
    cress
    co
    cuss
    cfv
    cV
    cuss
    cfv
    #
    @38
    crest
    co
    cT
    @39
    cA
    cvv
    cV
    ressuss
    ucnextcn.t
    cS
    @47
    @38
    crest
    ucnextcn.s
    oveq1i
    3eqtr4g
    fveq2d
    syl
    eleqtrrd
    @23
    vb
    @19
    cF
    vb
    cv
    #
    cima
    #
    cmpt
    va
    vb
    @19
    @22
    @49
    @21
    @48
    cF
    imaeq2
    cbvmptv
    rneqi
    fmucnd
    cU
    @24
    cY
    cfilufg
    syl2anc
    eqeltrd
    cnextucn
end
