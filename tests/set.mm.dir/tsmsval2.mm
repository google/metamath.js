include "cvv.mm"
include "cv.mm"
include "cdm.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cres.mm"
include "cgsu.mm"
include "co.mm"
include "cmpt.mm"
include "ctopn.mm"
include "cfv.mm"
include "wss.mm"
include "crab.mm"
include "crn.mm"
include "cfg.mm"
include "cflf.mm"
include "csb.mm"
include "ctsu.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-tsms.mm"
include "a1i.mm"
include "wa.mm"
include "wcel.mm"
include "vex.mm"
include "dmex.mm"
include "pwex.mm"
include "inex1.mm"
include "simplrl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "id.mm"
include "simprr.mm"
include "dmeqd.mm"
include "adantr.mm"
include "eqtrd.mm"
include "pweqd.mm"
include "ineq1d.mm"
include "sylan9eqr.mm"
include "rabeq.mm"
include "syl.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "oveq12d.mm"
include "simplrr.mm"
include "reseq1d.mm"
include "fveq12d.mm"
include "csbied.mm"
include "elex.mm"
include "fvexd.mm"
include "ovmpt2d.mm"

theorem tsmsval2
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cG: class G
  let cJ: class J
  let cL: class L
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vs: setvar s
  let vw: setvar w
  assume tsmsval.b: |- B = ( Base ` G )
  assume tsmsval.j: |- J = ( TopOpen ` G )
  assume tsmsval.s: |- S = ( ~P A i^i Fin )
  assume tsmsval.l: |- L = ran ( z e. S |-> { y e. S | z C_ y } )
  assume tsmsval.g: |- ( ph -> G e. V )
  assume tsmsval2.f: |- ( ph -> F e. W )
  assume tsmsval2.a: |- ( ph -> dom F = A )

  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G y
  disjoint G z
  disjoint ph y
  disjoint ph z
  disjoint S y
  disjoint f s
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint s w
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint G f
  disjoint G s
  disjoint G w
  disjoint f ph
  disjoint ph s
  disjoint ph w
  disjoint S f
  disjoint S s
  disjoint S w
  disjoint J f
  disjoint J s
  disjoint J w
  disjoint L f
  disjoint L s
  disjoint L w
  assert |- ( ph -> ( G tsums F ) = ( ( J fLimf ( S filGen L ) ) ` ( y e. S |-> ( G gsum ( F |` y ) ) ) ) )

  proof
    wph
    vw
    vf
    cG
    cF
    cvv
    cvv
    vs
    vf
    cv
    #
    cdm
    #
    cpw
    #
    cfn
    cin
    #
    vy
    vs
    cv
    #
    vw
    cv
    #
    @0
    vy
    cv
    #
    cres
    #
    cgsu
    co
    #
    cmpt
    #
    @5
    ctopn
    cfv
    #
    @4
    vz
    @4
    vz
    cv
    @6
    wss
    #
    vy
    @4
    crab
    #
    cmpt
    #
    crn
    #
    cfg
    co
    #
    cflf
    co
    #
    cfv
    #
    csb
    #
    vy
    cS
    cG
    cF
    @6
    cres
    #
    cgsu
    co
    #
    cmpt
    #
    cJ
    cS
    cL
    cfg
    co
    #
    cflf
    co
    #
    cfv
    #
    ctsu
    cvv
    ctsu
    vw
    vf
    cvv
    cvv
    @18
    cmpt2
    wceq
    wph
    vy
    vz
    vw
    vf
    vs
    df-tsms
    a1i
    wph
    @5
    cG
    wceq
    #
    @0
    cF
    wceq
    #
    wa
    #
    wa
    #
    vs
    @3
    @17
    @24
    cvv
    @3
    cvv
    wcel
    @28
    @2
    cfn
    @1
    @0
    vf
    vex
    dmex
    pwex
    inex1
    a1i
    @28
    @4
    @3
    wceq
    #
    wa
    #
    @9
    @21
    @16
    @23
    @30
    @10
    cJ
    @15
    @22
    cflf
    @30
    @10
    cG
    ctopn
    cfv
    cJ
    @30
    @5
    cG
    ctopn
    wph
    @25
    @26
    @29
    simplrl
    #
    fveq2d
    tsmsval.j
    syl6eqr
    @30
    @4
    cS
    @14
    cL
    cfg
    @29
    @28
    @4
    @3
    cS
    @29
    id
    @28
    @3
    cA
    cpw
    #
    cfn
    cin
    cS
    @28
    @2
    @32
    cfn
    @28
    @1
    cA
    @28
    @1
    cF
    cdm
    #
    cA
    @28
    @0
    cF
    wph
    @25
    @26
    simprr
    dmeqd
    wph
    @33
    cA
    wceq
    @27
    tsmsval2.a
    adantr
    eqtrd
    pweqd
    ineq1d
    tsmsval.s
    syl6eqr
    sylan9eqr
    #
    @30
    @14
    vz
    cS
    @11
    vy
    cS
    crab
    #
    cmpt
    #
    crn
    cL
    @30
    @13
    @36
    @30
    vz
    @4
    @12
    cS
    @35
    @34
    @30
    @4
    cS
    wceq
    @12
    @35
    wceq
    @34
    @11
    vy
    @4
    cS
    rabeq
    syl
    mpteq12dv
    rneqd
    tsmsval.l
    syl6eqr
    oveq12d
    oveq12d
    @30
    vy
    @4
    @8
    cS
    @20
    @34
    @30
    @5
    cG
    @7
    @19
    cgsu
    @31
    @30
    @0
    cF
    @6
    wph
    @25
    @26
    @29
    simplrr
    reseq1d
    oveq12d
    mpteq12dv
    fveq12d
    csbied
    wph
    cG
    cV
    wcel
    cG
    cvv
    wcel
    tsmsval.g
    cG
    cV
    elex
    syl
    wph
    cF
    cW
    wcel
    cF
    cvv
    wcel
    tsmsval2.f
    cF
    cW
    elex
    syl
    wph
    @21
    @23
    fvexd
    ovmpt2d
end
