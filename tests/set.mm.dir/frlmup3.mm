include "cuvc.mm"
include "co.mm"
include "crn.mm"
include "clspn.mm"
include "cfv.mm"
include "cima.mm"
include "clmhm.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "frlmup1.mm"
include "wf.mm"
include "crg.mm"
include "csca.mm"
include "clmod.mm"
include "eqid.mm"
include "lmodring.mm"
include "syl.mm"
include "eqeltrd.mm"
include "uvcff.mm"
include "syl2anc.mm"
include "frn.mm"
include "lmhmlsp.mm"
include "wfn.mm"
include "lmhmf.mm"
include "ffn.mm"
include "fnima.mm"
include "clbs.mm"
include "frlmlbs.mm"
include "lbssp.mm"
include "eqcomd.mm"
include "imaeq2d.mm"
include "eqtr3d.mm"
include "ccom.mm"
include "imaco.mm"
include "fnco.mm"
include "syl3anc.mm"
include "cv.mm"
include "wa.mm"
include "fvco2.mm"
include "sylan.mm"
include "adantr.mm"
include "simpr.mm"
include "frlmup2.mm"
include "eqtr2d.mm"
include "eqfnfvd.mm"
include "imaeq1d.mm"
include "3eqtr3a.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"

theorem frlmup3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let cE: class E
  let cF: class F
  let cI: class I
  let cK: class K
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cY: class Y
  let cU: class U
  let vu: setvar u
  assume frlmup.f: |- F = ( R freeLMod I )
  assume frlmup.b: |- B = ( Base ` F )
  assume frlmup.c: |- C = ( Base ` T )
  assume frlmup.v: |- .x. = ( .s ` T )
  assume frlmup.e: |- E = ( x e. B |-> ( T gsum ( x oF .x. A ) ) )
  assume frlmup.t: |- ( ph -> T e. LMod )
  assume frlmup.i: |- ( ph -> I e. X )
  assume frlmup.r: |- ( ph -> R = ( Scalar ` T ) )
  assume frlmup.a: |- ( ph -> A : I --> C )
  assume frlmup.k: |- K = ( LSpan ` T )

  disjoint R x
  disjoint I x
  disjoint F x
  disjoint B x
  disjoint C x
  disjoint .x. x
  disjoint A x
  disjoint X x
  disjoint K x
  disjoint ph x
  disjoint T x
  disjoint R y
  disjoint R z
  disjoint R w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint I y
  disjoint I z
  disjoint I w
  disjoint F y
  disjoint F z
  disjoint F w
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint C y
  disjoint C z
  disjoint C w
  disjoint .x. y
  disjoint .x. z
  disjoint .x. w
  disjoint E y
  disjoint E z
  disjoint E w
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint X y
  disjoint X z
  disjoint X w
  disjoint K y
  disjoint K z
  disjoint K w
  disjoint ph y
  disjoint ph z
  disjoint ph w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint Y w
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint U w
  disjoint T y
  disjoint T z
  disjoint T w
  disjoint ph u
  disjoint I u
  disjoint u x
  disjoint A u
  disjoint E u
  disjoint R u
  assert |- ( ph -> ran E = ( K ` ran A ) )

  proof
    wph
    cE
    cR
    cI
    cuvc
    co
    #
    crn
    #
    cF
    clspn
    cfv
    #
    cfv
    #
    cima
    #
    cE
    @1
    cima
    #
    cK
    cfv
    #
    cE
    crn
    #
    cA
    crn
    #
    cK
    cfv
    wph
    cE
    cF
    cT
    clmhm
    co
    wcel
    #
    @1
    cB
    wss
    #
    @4
    @6
    wceq
    wph
    vx
    cA
    cB
    cC
    cR
    cT
    c.x
    cE
    cF
    cI
    cX
    frlmup.f
    frlmup.b
    frlmup.c
    frlmup.v
    frlmup.e
    frlmup.t
    frlmup.i
    frlmup.r
    frlmup.a
    frlmup1
    #
    wph
    cI
    cB
    @0
    wf
    #
    @10
    wph
    cR
    crg
    wcel
    #
    cI
    cX
    wcel
    #
    @12
    wph
    cR
    cT
    csca
    cfv
    #
    crg
    frlmup.r
    wph
    cT
    clmod
    wcel
    #
    @15
    crg
    wcel
    frlmup.t
    @15
    cT
    @15
    eqid
    lmodring
    syl
    eqeltrd
    #
    frlmup.i
    cB
    cR
    @0
    cI
    cX
    cF
    @0
    eqid
    #
    frlmup.f
    frlmup.b
    uvcff
    syl2anc
    #
    cI
    cB
    @0
    frn
    syl
    #
    cF
    cT
    @1
    cE
    @2
    cK
    cB
    frlmup.b
    @2
    eqid
    #
    frlmup.k
    lmhmlsp
    syl2anc
    wph
    cE
    cB
    cima
    #
    @7
    @4
    wph
    cE
    cB
    wfn
    #
    @22
    @7
    wceq
    wph
    cB
    cC
    cE
    wf
    #
    @23
    wph
    @9
    @24
    @11
    cB
    cC
    cF
    cT
    cE
    frlmup.b
    frlmup.c
    lmhmf
    syl
    cB
    cC
    cE
    ffn
    syl
    #
    cB
    cE
    fnima
    syl
    wph
    cB
    @3
    cE
    wph
    @3
    cB
    wph
    @1
    cF
    clbs
    cfv
    #
    wcel
    #
    @3
    cB
    wceq
    wph
    @13
    @14
    @27
    @17
    frlmup.i
    cR
    @0
    cF
    cI
    @26
    cX
    frlmup.f
    @18
    @26
    eqid
    #
    frlmlbs
    syl2anc
    @1
    @26
    @2
    cB
    cF
    frlmup.b
    @28
    @21
    lbssp
    syl
    eqcomd
    imaeq2d
    eqtr3d
    wph
    @8
    @5
    cK
    wph
    cE
    @0
    ccom
    #
    cI
    cima
    #
    cE
    @0
    cI
    cima
    #
    cima
    @8
    @5
    cE
    @0
    cI
    imaco
    wph
    cA
    cI
    cima
    #
    @30
    @8
    wph
    cA
    @29
    cI
    wph
    vu
    cI
    cA
    @29
    wph
    cI
    cC
    cA
    wf
    #
    cA
    cI
    wfn
    #
    frlmup.a
    cI
    cC
    cA
    ffn
    syl
    #
    wph
    @23
    @0
    cI
    wfn
    #
    @10
    @29
    cI
    wfn
    @25
    wph
    @12
    @36
    @19
    cI
    cB
    @0
    ffn
    syl
    #
    @20
    cB
    cI
    cE
    @0
    fnco
    syl3anc
    wph
    vu
    cv
    #
    cI
    wcel
    #
    wa
    #
    @38
    @29
    cfv
    #
    @38
    @0
    cfv
    cE
    cfv
    #
    @38
    cA
    cfv
    wph
    @36
    @39
    @41
    @42
    wceq
    @37
    cI
    cE
    @0
    @38
    fvco2
    sylan
    @40
    vx
    cA
    cB
    cC
    cR
    cT
    c.x
    @0
    cE
    cF
    cI
    cX
    @38
    frlmup.f
    frlmup.b
    frlmup.c
    frlmup.v
    frlmup.e
    wph
    @16
    @39
    frlmup.t
    adantr
    wph
    @14
    @39
    frlmup.i
    adantr
    wph
    cR
    @15
    wceq
    @39
    frlmup.r
    adantr
    wph
    @33
    @39
    frlmup.a
    adantr
    wph
    @39
    simpr
    @18
    frlmup2
    eqtr2d
    eqfnfvd
    imaeq1d
    wph
    @34
    @32
    @8
    wceq
    @35
    cI
    cA
    fnima
    syl
    eqtr3d
    wph
    @31
    @1
    cE
    wph
    @36
    @31
    @1
    wceq
    @37
    cI
    @0
    fnima
    syl
    imaeq2d
    3eqtr3a
    fveq2d
    3eqtr4d
end
