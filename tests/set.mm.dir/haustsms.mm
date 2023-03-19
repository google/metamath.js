include "cv.mm"
include "ctsu.mm"
include "co.mm"
include "wcel.mm"
include "wmo.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cres.mm"
include "cgsu.mm"
include "cmpt.mm"
include "wss.mm"
include "crab.mm"
include "crn.mm"
include "cfg.mm"
include "cflf.mm"
include "cfv.mm"
include "cha.mm"
include "cfil.mm"
include "cuni.mm"
include "wf.mm"
include "cfbas.mm"
include "eqid.mm"
include "tsmsfbas.mm"
include "fgcl.mm"
include "syl.mm"
include "wa.mm"
include "tsmslem1.mm"
include "wceq.mm"
include "ctps.mm"
include "tpsuni.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "fmptd.mm"
include "hausflf.mm"
include "syl3anc.mm"
include "ccmn.mm"
include "tsmsval.mm"
include "eleq2d.mm"
include "mobidv.mm"
include "mpbird.mm"

theorem haustsms
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cJ: class J
  let cV: class V
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  assume tsmscl.b: |- B = ( Base ` G )
  assume tsmscl.1: |- ( ph -> G e. CMnd )
  assume tsmscl.2: |- ( ph -> G e. TopSp )
  assume tsmscl.a: |- ( ph -> A e. V )
  assume tsmscl.f: |- ( ph -> F : A --> B )
  assume haustsms.j: |- J = ( TopOpen ` G )
  assume haustsms.h: |- ( ph -> J e. Haus )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint G x
  disjoint J x
  disjoint ph x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint G w
  disjoint G y
  disjoint G z
  disjoint X x
  disjoint J z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> E* x x e. ( G tsums F ) )

  proof
    wph
    vx
    cv
    #
    cG
    cF
    ctsu
    co
    #
    wcel
    #
    vx
    wmo
    @0
    vz
    cA
    cpw
    cfn
    cin
    #
    cG
    cF
    vz
    cv
    #
    cres
    cgsu
    co
    #
    cmpt
    #
    cJ
    @3
    vy
    @3
    vy
    cv
    @4
    wss
    vz
    @3
    crab
    cmpt
    #
    crn
    #
    cfg
    co
    #
    cflf
    co
    cfv
    #
    wcel
    #
    vx
    wmo
    #
    wph
    cJ
    cha
    wcel
    @9
    @3
    cfil
    cfv
    wcel
    #
    @3
    cJ
    cuni
    #
    @6
    wf
    @12
    haustsms.h
    wph
    @8
    @3
    cfbas
    cfv
    wcel
    @13
    wph
    vz
    vy
    cA
    @3
    @7
    @8
    cV
    @3
    eqid
    #
    @7
    eqid
    @8
    eqid
    #
    tsmscl.a
    tsmsfbas
    @8
    @3
    fgcl
    syl
    wph
    vz
    @3
    @5
    @14
    @6
    wph
    @4
    @3
    wcel
    #
    wa
    @5
    cB
    @14
    wph
    cA
    cB
    @3
    cF
    cG
    cV
    @4
    tsmscl.b
    @15
    tsmscl.1
    tsmscl.a
    tsmscl.f
    tsmslem1
    wph
    cB
    @14
    wceq
    #
    @17
    wph
    cG
    ctps
    wcel
    @18
    tsmscl.2
    cB
    cJ
    cG
    tsmscl.b
    haustsms.j
    tpsuni
    syl
    adantr
    eleqtrd
    @6
    eqid
    fmptd
    vx
    @6
    cJ
    @9
    @14
    @3
    @14
    eqid
    hausflf
    syl3anc
    wph
    @2
    @11
    vx
    wph
    @1
    @10
    @0
    wph
    vz
    vy
    cA
    cB
    @3
    cF
    cG
    cJ
    @8
    ccmn
    cV
    tsmscl.b
    haustsms.j
    @15
    @16
    tsmscl.1
    tsmscl.a
    tsmscl.f
    tsmsval
    eleq2d
    mobidv
    mpbird
end
