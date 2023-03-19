include "ccom.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "crli.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "cc.mm"
include "fveq2.mm"
include "fmptco.mm"
include "wbr.mm"
include "cle.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "fvexd.mm"
include "ralrimiva.mm"
include "simpr.mm"
include "eqbrtrrd.mm"
include "ad2antrr.mm"
include "rlimi.mm"
include "simpll.mm"
include "sylan.mm"
include "simplrr.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "oveq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "reximdv.mm"
include "expr.mm"
include "mpid.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "syldan.mm"
include "cdm.mm"
include "wf.mm"
include "fdm.mm"
include "syl.mm"
include "wss.mm"
include "rlimss.mm"
include "eqsstr3d.mm"
include "ffvelrnd.mm"
include "rlim2.mm"
include "mpbird.mm"
include "eqbrtrd.mm"

theorem rlimcn1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cF: class F
  let cG: class G
  let cX: class X
  let vc: setvar c
  let vw: setvar w
  let vv: setvar v
  assume rlimcn1.1: |- ( ph -> G : A --> X )
  assume rlimcn1.2: |- ( ph -> C e. X )
  assume rlimcn1.3: |- ( ph -> G ~~>r C )
  assume rlimcn1.4: |- ( ph -> F : X --> CC )
  assume rlimcn1.5: |- ( ( ph /\ x e. RR+ ) -> E. y e. RR+ A. z e. X ( ( abs ` ( z - C ) ) < y -> ( abs ` ( ( F ` z ) - ( F ` C ) ) ) < x ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph x
  disjoint ph y
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint X z
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint c v
  disjoint c z
  disjoint F c
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w z
  disjoint F w
  disjoint G c
  disjoint G v
  disjoint G w
  disjoint c ph
  disjoint ph w
  disjoint C c
  disjoint C w
  disjoint X c
  disjoint X v
  disjoint X w
  assert |- ( ph -> ( F o. G ) ~~>r ( F ` C ) )

  proof
    wph
    cF
    cG
    ccom
    vw
    cA
    vw
    cv
    #
    cG
    cfv
    #
    cF
    cfv
    #
    cmpt
    #
    cC
    cF
    cfv
    #
    crli
    wph
    vw
    vv
    cA
    cX
    @1
    vv
    cv
    #
    cF
    cfv
    @2
    cG
    cF
    wph
    cA
    cX
    @0
    cG
    rlimcn1.1
    ffvelrnda
    #
    wph
    vw
    cA
    cX
    cG
    rlimcn1.1
    feqmptd
    #
    wph
    vv
    cX
    cc
    cF
    rlimcn1.4
    feqmptd
    @5
    @1
    cF
    fveq2
    fmptco
    wph
    @3
    @4
    crli
    wbr
    vc
    cv
    @0
    cle
    wbr
    #
    @2
    @4
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    cA
    wral
    #
    vc
    cr
    wrex
    #
    vx
    crp
    wral
    wph
    @15
    vx
    crp
    wph
    @11
    crp
    wcel
    #
    wa
    #
    vz
    cv
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    @18
    cF
    cfv
    #
    @4
    cmin
    co
    #
    cabs
    cfv
    #
    @11
    clt
    wbr
    #
    wi
    #
    vz
    cX
    wral
    #
    vy
    crp
    wrex
    @15
    rlimcn1.5
    @17
    @28
    @15
    vy
    crp
    @17
    @21
    crp
    wcel
    #
    wa
    #
    @28
    @8
    @1
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    @21
    clt
    wbr
    #
    wi
    #
    vw
    cA
    wral
    #
    vc
    cr
    wrex
    #
    @15
    @30
    vc
    vw
    cA
    @1
    cC
    @21
    cvv
    @30
    @1
    cvv
    wcel
    vw
    cA
    @30
    @0
    cA
    wcel
    #
    wa
    @0
    cG
    fvexd
    ralrimiva
    @17
    @29
    simpr
    wph
    vw
    cA
    @1
    cmpt
    #
    cC
    crli
    wbr
    @16
    @29
    wph
    cG
    @38
    cC
    crli
    @7
    rlimcn1.3
    eqbrtrrd
    ad2antrr
    rlimi
    @17
    @29
    @28
    @36
    @15
    wi
    @17
    @29
    @28
    wa
    #
    wa
    #
    @35
    @14
    vc
    cr
    @40
    @34
    @13
    vw
    cA
    @40
    @37
    wa
    #
    @33
    @12
    @8
    @41
    @1
    cX
    wcel
    #
    @28
    @33
    @12
    wi
    #
    @40
    wph
    @37
    @42
    wph
    @16
    @39
    simpll
    @6
    sylan
    @17
    @29
    @28
    @37
    simplrr
    @27
    @43
    vz
    @1
    cX
    @18
    @1
    wceq
    #
    @22
    @33
    @26
    @12
    @44
    @20
    @32
    @21
    clt
    @44
    @19
    @31
    cabs
    @18
    @1
    cC
    cmin
    oveq1
    fveq2d
    breq1d
    @44
    @25
    @10
    @11
    clt
    @44
    @24
    @9
    cabs
    @44
    @23
    @2
    @4
    cmin
    @18
    @1
    cF
    fveq2
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rspcv
    sylc
    imim2d
    ralimdva
    reximdv
    expr
    mpid
    rexlimdva
    mpd
    ralrimiva
    wph
    vx
    vc
    vw
    cA
    @2
    @4
    wph
    @2
    cc
    wcel
    #
    vw
    cA
    wph
    @37
    @42
    @45
    @6
    wph
    cX
    cc
    @1
    cF
    rlimcn1.4
    ffvelrnda
    syldan
    ralrimiva
    wph
    cA
    cG
    cdm
    #
    cr
    wph
    cA
    cX
    cG
    wf
    @46
    cA
    wceq
    rlimcn1.1
    cA
    cX
    cG
    fdm
    syl
    wph
    cG
    cC
    crli
    wbr
    @46
    cr
    wss
    rlimcn1.3
    cC
    cG
    rlimss
    syl
    eqsstr3d
    wph
    cX
    cc
    cC
    cF
    rlimcn1.4
    rlimcn1.2
    ffvelrnd
    rlim2
    mpbird
    eqbrtrd
end
