include "csn.mm"
include "ccl.mm"
include "cfv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "cfg.mm"
include "co.mm"
include "cres.mm"
include "cgsu.mm"
include "cfm.mm"
include "cflim.mm"
include "ctsu.mm"
include "wcel.mm"
include "cflf.mm"
include "ctps.mm"
include "eqid.mm"
include "tsmsval.mm"
include "ctopon.mm"
include "cfil.mm"
include "wf.mm"
include "wceq.mm"
include "istps.mm"
include "sylib.mm"
include "cfbas.mm"
include "tsmsfbas.mm"
include "fgcl.mm"
include "syl.mm"
include "tsmslem1.mm"
include "fmptd.mm"
include "flfval.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "eleqtrd.mm"
include "flimsncls.mm"
include "sseqtr4d.mm"

theorem tsmscls
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cJ: class J
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume tsmscls.b: |- B = ( Base ` G )
  assume tsmscls.j: |- J = ( TopOpen ` G )
  assume tsmscls.1: |- ( ph -> G e. CMnd )
  assume tsmscls.2: |- ( ph -> G e. TopSp )
  assume tsmscls.a: |- ( ph -> A e. V )
  assume tsmscls.f: |- ( ph -> F : A --> B )
  assume tsmscls.x: |- ( ph -> X e. ( G tsums F ) )


  assert |- ( ph -> ( ( cls ` J ) ` { X } ) C_ ( G tsums F ) )

  proof
    wph
    cX
    csn
    cJ
    ccl
    cfv
    cfv
    #
    cJ
    cA
    cpw
    cfn
    cin
    #
    vx
    @1
    vx
    cv
    vy
    cv
    #
    wss
    vy
    @1
    crab
    cmpt
    #
    crn
    #
    cfg
    co
    #
    cB
    vy
    @1
    cG
    cF
    @2
    cres
    cgsu
    co
    #
    cmpt
    #
    cfm
    co
    cfv
    #
    cflim
    co
    #
    cG
    cF
    ctsu
    co
    #
    wph
    cX
    @9
    wcel
    @0
    @9
    wss
    wph
    cX
    @10
    @9
    tsmscls.x
    wph
    @10
    @7
    cJ
    @5
    cflf
    co
    cfv
    #
    @9
    wph
    vy
    vx
    cA
    cB
    @1
    cF
    cG
    cJ
    @4
    ctps
    cV
    tsmscls.b
    tsmscls.j
    @1
    eqid
    #
    @4
    eqid
    #
    tsmscls.2
    tsmscls.a
    tsmscls.f
    tsmsval
    wph
    cJ
    cB
    ctopon
    cfv
    wcel
    #
    @5
    @1
    cfil
    cfv
    wcel
    #
    @1
    cB
    @7
    wf
    @11
    @9
    wceq
    wph
    cG
    ctps
    wcel
    @14
    tsmscls.2
    cB
    cJ
    cG
    tsmscls.b
    tsmscls.j
    istps
    sylib
    wph
    @4
    @1
    cfbas
    cfv
    wcel
    @15
    wph
    vy
    vx
    cA
    @1
    @3
    @4
    cV
    @12
    @3
    eqid
    @13
    tsmscls.a
    tsmsfbas
    @4
    @1
    fgcl
    syl
    wph
    vy
    @1
    @6
    cB
    @7
    wph
    cA
    cB
    @1
    cF
    cG
    cV
    @2
    tsmscls.b
    @12
    tsmscls.1
    tsmscls.a
    tsmscls.f
    tsmslem1
    @7
    eqid
    fmptd
    @7
    cJ
    @5
    cB
    @1
    flfval
    syl3anc
    eqtrd
    #
    eleqtrd
    cX
    @8
    cJ
    flimsncls
    syl
    @16
    sseqtr4d
end
