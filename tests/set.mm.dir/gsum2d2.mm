include "cmpt2.mm"
include "cgsu.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "cima.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "snex.mm"
include "xpexg.mm"
include "sylancr.mm"
include "ralrimiva.mm"
include "iunexg.mm"
include "syl2anc.mm"
include "wrel.mm"
include "relxp.mm"
include "rgenw.mm"
include "reliun.mm"
include "mpbir.mm"
include "a1i.mm"
include "cdm.mm"
include "cop.mm"
include "wex.mm"
include "vex.mm"
include "eldm2.mm"
include "wceq.mm"
include "eliunxp.mm"
include "opth1.mm"
include "ad2antrl.mm"
include "simprrl.mm"
include "eqeltrd.mm"
include "ex.mm"
include "exlimdvv.mm"
include "syl5bi.mm"
include "exlimdv.mm"
include "ssrdv.mm"
include "wf.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "fmpt2x.mm"
include "sylib.mm"
include "gsum2d2lem.mm"
include "gsum2d.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nfima.mm"
include "nfmpt21.mm"
include "nfov.mm"
include "nfmpt.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "oveq1.mm"
include "mpteq12dv.mm"
include "oveq2d.mm"
include "cbvmpt.mm"
include "elimasn.mm"
include "opeliunxp.mm"
include "bitri.mm"
include "baib.mm"
include "eqrdv.mm"
include "mpteq1d.mm"
include "nfmpt22.mm"
include "oveq2.mm"
include "syl6eq.mm"
include "adantl.mm"
include "simprl.mm"
include "simprr.mm"
include "ovmpt4g.mm"
include "syl3anc.mm"
include "anassrs.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem gsum2d2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let vj: setvar j
  let vk: setvar k
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cE: class E
  assume gsum2d2.b: |- B = ( Base ` G )
  assume gsum2d2.z: |- .0. = ( 0g ` G )
  assume gsum2d2.g: |- ( ph -> G e. CMnd )
  assume gsum2d2.a: |- ( ph -> A e. V )
  assume gsum2d2.r: |- ( ( ph /\ j e. A ) -> C e. W )
  assume gsum2d2.f: |- ( ( ph /\ ( j e. A /\ k e. C ) ) -> X e. B )
  assume gsum2d2.u: |- ( ph -> U e. Fin )
  assume gsum2d2.n: |- ( ( ph /\ ( ( j e. A /\ k e. C ) /\ -. j U k ) ) -> X = .0. )

  disjoint j k
  disjoint B j
  disjoint B k
  disjoint j ph
  disjoint k ph
  disjoint A j
  disjoint A k
  disjoint G j
  disjoint G k
  disjoint U j
  disjoint U k
  disjoint C k
  disjoint V j
  disjoint .0. j
  disjoint .0. k
  disjoint j m
  disjoint j n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint B m
  disjoint B n
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint D j
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint D k
  disjoint x y
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint E j
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint m ph
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint U z
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint C m
  disjoint C n
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint .0. m
  disjoint .0. n
  disjoint .0. x
  disjoint .0. z
  assert |- ( ph -> ( G gsum ( j e. A , k e. C |-> X ) ) = ( G gsum ( j e. A |-> ( G gsum ( k e. C |-> X ) ) ) ) )

  proof
    wph
    cG
    vj
    vk
    cA
    cC
    cX
    cmpt2
    #
    cgsu
    co
    cG
    vm
    cA
    cG
    vn
    vj
    cA
    vj
    cv
    #
    csn
    #
    cC
    cxp
    #
    ciun
    #
    vm
    cv
    #
    csn
    #
    cima
    #
    @5
    vn
    cv
    #
    @0
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    cG
    vj
    cA
    cG
    vk
    cC
    cX
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    wph
    @4
    cB
    cA
    vm
    vn
    @0
    cG
    cvv
    cV
    c.0
    gsum2d2.b
    gsum2d2.z
    gsum2d2.g
    wph
    cA
    cV
    wcel
    @3
    cvv
    wcel
    #
    vj
    cA
    wral
    @4
    cvv
    wcel
    gsum2d2.a
    wph
    @16
    vj
    cA
    wph
    @1
    cA
    wcel
    #
    wa
    #
    @2
    cvv
    wcel
    cC
    cW
    wcel
    @16
    @1
    snex
    gsum2d2.r
    @2
    cC
    cvv
    cW
    xpexg
    sylancr
    ralrimiva
    vj
    cA
    @3
    cV
    cvv
    iunexg
    syl2anc
    @4
    wrel
    #
    wph
    @19
    @3
    wrel
    #
    vj
    cA
    wral
    @20
    vj
    cA
    @2
    cC
    relxp
    rgenw
    vj
    cA
    @3
    reliun
    mpbir
    a1i
    gsum2d2.a
    wph
    vx
    @4
    cdm
    #
    cA
    vx
    cv
    #
    @21
    wcel
    @22
    vy
    cv
    #
    cop
    #
    @4
    wcel
    #
    vy
    wex
    wph
    @22
    cA
    wcel
    #
    vy
    @22
    @4
    vx
    vex
    #
    eldm2
    wph
    @25
    @26
    vy
    @25
    @24
    @1
    vk
    cv
    #
    cop
    #
    wceq
    #
    @17
    @28
    cC
    wcel
    #
    wa
    #
    wa
    #
    vk
    wex
    vj
    wex
    wph
    @26
    vj
    vk
    cA
    cC
    @24
    eliunxp
    wph
    @33
    @26
    vj
    vk
    wph
    @33
    @26
    wph
    @33
    wa
    @22
    @1
    cA
    @30
    @22
    @1
    wceq
    wph
    @32
    @22
    @23
    @1
    @28
    @27
    vy
    vex
    opth1
    ad2antrl
    wph
    @30
    @17
    @31
    simprrl
    eqeltrd
    ex
    exlimdvv
    syl5bi
    exlimdv
    syl5bi
    ssrdv
    wph
    cX
    cB
    wcel
    #
    vk
    cC
    wral
    vj
    cA
    wral
    @4
    cB
    @0
    wf
    wph
    @34
    vj
    vk
    cA
    cC
    gsum2d2.f
    ralrimivva
    vj
    vk
    cA
    cC
    cX
    cB
    @0
    @0
    eqid
    #
    fmpt2x
    sylib
    wph
    cA
    cB
    cC
    cU
    vj
    vk
    cG
    cV
    cW
    cX
    c.0
    gsum2d2.b
    gsum2d2.z
    gsum2d2.g
    gsum2d2.a
    gsum2d2.r
    gsum2d2.f
    gsum2d2.u
    gsum2d2.n
    gsum2d2lem
    gsum2d
    wph
    @12
    @15
    cG
    cgsu
    wph
    @12
    vj
    cA
    cG
    vn
    @4
    @2
    cima
    #
    @1
    @8
    @0
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    @15
    vm
    vj
    cA
    @11
    @39
    vj
    cG
    @10
    cgsu
    vj
    cG
    nfcv
    vj
    cgsu
    nfcv
    vj
    vn
    @7
    @9
    vj
    @4
    @6
    vj
    cA
    @3
    nfiu1
    vj
    @6
    nfcv
    nfima
    vj
    @5
    @8
    @0
    vj
    @5
    nfcv
    vj
    vk
    cA
    cC
    cX
    nfmpt21
    vj
    @8
    nfcv
    nfov
    nfmpt
    nfov
    vm
    @39
    nfcv
    @5
    @1
    wceq
    #
    @10
    @38
    cG
    cgsu
    @40
    vn
    @7
    @9
    @36
    @37
    @40
    @6
    @2
    @4
    @5
    @1
    sneq
    imaeq2d
    @5
    @1
    @8
    @0
    oveq1
    mpteq12dv
    oveq2d
    cbvmpt
    wph
    vj
    cA
    @39
    @14
    @18
    @38
    @13
    cG
    cgsu
    @18
    @38
    vk
    cC
    @1
    @28
    @0
    co
    #
    cmpt
    #
    @13
    @17
    @38
    @42
    wceq
    wph
    @17
    @38
    vn
    cC
    @37
    cmpt
    @42
    @17
    vn
    @36
    cC
    @37
    @17
    vk
    @36
    cC
    @28
    @36
    wcel
    #
    @17
    @31
    @43
    @29
    @4
    wcel
    @32
    @4
    @1
    @28
    vj
    vex
    vk
    vex
    elimasn
    vj
    cA
    cC
    @28
    opeliunxp
    bitri
    baib
    eqrdv
    mpteq1d
    vn
    vk
    cC
    @37
    @41
    vk
    @1
    @8
    @0
    vk
    @1
    nfcv
    vj
    vk
    cA
    cC
    cX
    nfmpt22
    vk
    @8
    nfcv
    nfov
    vn
    @41
    nfcv
    @8
    @28
    @1
    @0
    oveq2
    cbvmpt
    syl6eq
    adantl
    @18
    vk
    cC
    @41
    cX
    wph
    @17
    @31
    @41
    cX
    wceq
    #
    wph
    @32
    wa
    @17
    @31
    @34
    @44
    wph
    @17
    @31
    simprl
    wph
    @17
    @31
    simprr
    gsum2d2.f
    vj
    vk
    cA
    cC
    cX
    @0
    cB
    @35
    ovmpt4g
    syl3anc
    anassrs
    mpteq2dva
    eqtrd
    oveq2d
    mpteq2dva
    syl5eq
    oveq2d
    eqtrd
end
