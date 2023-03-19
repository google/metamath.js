include "cmpt2.mm"
include "cgsu.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "ccnv.mm"
include "cuni.mm"
include "cmpt.mm"
include "ccom.mm"
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
include "wf.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "fmpt2x.mm"
include "sylib.mm"
include "gsum2d2lem.mm"
include "wf1o.mm"
include "wrel.mm"
include "relxp.mm"
include "rgenw.mm"
include "reliun.mm"
include "mpbir.mm"
include "cnvf1o.mm"
include "ax-mp.mm"
include "wceq.mm"
include "wb.mm"
include "relcnv.mm"
include "cop.mm"
include "wi.mm"
include "nfv.mm"
include "nfiu1.mm"
include "nfcnv.mm"
include "nfel2.mm"
include "nfbi.mm"
include "nfim.mm"
include "weq.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "opeq1.mm"
include "opeliunxp.mm"
include "3bitr4g.mm"
include "vex.mm"
include "opelcnv.mm"
include "syl6bbr.mm"
include "chvar.mm"
include "eqrelrdv.mm"
include "f1oeq3.mm"
include "syl.mm"
include "mpbiri.mm"
include "gsumf1o.mm"
include "cfv.mm"
include "csb.mm"
include "sneq.mm"
include "cnveqd.mm"
include "unieqd.mm"
include "opswap.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "mpt2mptx.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfxp.mm"
include "csbeq1a.mm"
include "xpeq12d.mm"
include "cbviun.mm"
include "mpteq1.mm"
include "nfmpt22.mm"
include "nfov.mm"
include "nfmpt21.mm"
include "oveq2.mm"
include "oveq1.mm"
include "sylan9eq.mm"
include "cbvmpt2x.mm"
include "3eqtr4i.mm"
include "f1of.mm"
include "fmpt.mm"
include "sylibr.mm"
include "eqidd.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptcof.mm"
include "w3a.mm"
include "ex.mm"
include "ovmpt4g.mm"
include "3expia.mm"
include "sylcom.mm"
include "sylbird.mm"
include "3impib.mm"
include "eqcomd.mm"
include "mpt2eq3dva.mm"
include "3eqtr4a.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem gsumcom2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume gsum2d2.b: |- B = ( Base ` G )
  assume gsum2d2.z: |- .0. = ( 0g ` G )
  assume gsum2d2.g: |- ( ph -> G e. CMnd )
  assume gsum2d2.a: |- ( ph -> A e. V )
  assume gsum2d2.r: |- ( ( ph /\ j e. A ) -> C e. W )
  assume gsum2d2.f: |- ( ( ph /\ ( j e. A /\ k e. C ) ) -> X e. B )
  assume gsum2d2.u: |- ( ph -> U e. Fin )
  assume gsum2d2.n: |- ( ( ph /\ ( ( j e. A /\ k e. C ) /\ -. j U k ) ) -> X = .0. )
  assume gsumcom2.d: |- ( ph -> D e. Y )
  assume gsumcom2.c: |- ( ph -> ( ( j e. A /\ k e. C ) <-> ( k e. D /\ j e. E ) ) )

  disjoint j k
  disjoint B j
  disjoint B k
  disjoint D j
  disjoint D k
  disjoint E j
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
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
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
  assert |- ( ph -> ( G gsum ( j e. A , k e. C |-> X ) ) = ( G gsum ( k e. D , j e. E |-> X ) ) )

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
    @0
    vz
    vk
    cD
    vk
    cv
    #
    csn
    #
    cE
    cxp
    #
    ciun
    #
    vz
    cv
    #
    csn
    #
    ccnv
    #
    cuni
    #
    cmpt
    #
    ccom
    #
    cgsu
    co
    cG
    vk
    vj
    cD
    cE
    cX
    cmpt2
    #
    cgsu
    co
    wph
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
    cB
    @4
    @0
    cG
    @9
    cvv
    c.0
    gsum2d2.b
    gsum2d2.z
    gsum2d2.g
    wph
    cA
    cV
    wcel
    @14
    cvv
    wcel
    #
    vj
    cA
    wral
    @15
    cvv
    wcel
    gsum2d2.a
    wph
    @16
    vj
    cA
    wph
    @12
    cA
    wcel
    #
    wa
    @13
    cvv
    wcel
    cC
    cW
    wcel
    @16
    @12
    snex
    gsum2d2.r
    @13
    cC
    cvv
    cW
    xpexg
    sylancr
    ralrimiva
    vj
    cA
    @14
    cV
    cvv
    iunexg
    syl2anc
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
    @15
    cB
    @0
    wf
    wph
    @18
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
    #
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
    wph
    @4
    @15
    @9
    wf1o
    #
    @4
    @4
    ccnv
    #
    @9
    wf1o
    #
    @4
    wrel
    #
    @23
    @24
    @3
    wrel
    #
    vk
    cD
    wral
    @25
    vk
    cD
    @2
    cE
    relxp
    rgenw
    vk
    cD
    @3
    reliun
    mpbir
    vz
    @4
    cnvf1o
    ax-mp
    wph
    @15
    @22
    wceq
    @21
    @23
    wb
    wph
    vx
    vy
    @15
    @22
    @15
    wrel
    @14
    wrel
    #
    vj
    cA
    wral
    @26
    vj
    cA
    @13
    cC
    relxp
    rgenw
    vj
    cA
    @14
    reliun
    mpbir
    @4
    relcnv
    wph
    vx
    cv
    #
    @1
    cop
    #
    @15
    wcel
    #
    @28
    @22
    wcel
    #
    wb
    #
    wi
    #
    wph
    @27
    vy
    cv
    #
    cop
    #
    @15
    wcel
    #
    @34
    @22
    wcel
    #
    wb
    #
    wi
    vk
    vy
    wph
    @37
    vk
    wph
    vk
    nfv
    @35
    @36
    vk
    @35
    vk
    nfv
    vk
    @34
    @22
    vk
    @4
    vk
    cD
    @3
    nfiu1
    nfcnv
    nfel2
    nfbi
    nfim
    vk
    vy
    weq
    #
    @31
    @37
    wph
    @38
    @29
    @35
    @30
    @36
    @38
    @28
    @34
    @15
    @1
    @33
    @27
    opeq2
    #
    eleq1d
    @38
    @28
    @34
    @22
    @39
    eleq1d
    bibi12d
    imbi2d
    wph
    @12
    @1
    cop
    #
    @15
    wcel
    #
    @40
    @22
    wcel
    #
    wb
    #
    wi
    @32
    vj
    vx
    wph
    @31
    vj
    wph
    vj
    nfv
    @29
    @30
    vj
    vj
    @28
    @15
    vj
    cA
    @14
    nfiu1
    nfel2
    @30
    vj
    nfv
    nfbi
    nfim
    vj
    vx
    weq
    #
    @43
    @31
    wph
    @44
    @41
    @29
    @42
    @30
    @44
    @40
    @28
    @15
    @12
    @27
    @1
    opeq1
    #
    eleq1d
    @44
    @40
    @28
    @22
    @45
    eleq1d
    bibi12d
    imbi2d
    wph
    @41
    @1
    @12
    cop
    @4
    wcel
    #
    @42
    wph
    @17
    @1
    cC
    wcel
    #
    wa
    #
    @1
    cD
    wcel
    #
    @12
    cE
    wcel
    #
    wa
    #
    @41
    @46
    gsumcom2.c
    vj
    cA
    cC
    @1
    opeliunxp
    vk
    cD
    cE
    @12
    opeliunxp
    3bitr4g
    @12
    @1
    @4
    vj
    vex
    vk
    vex
    opelcnv
    syl6bbr
    chvar
    chvar
    eqrelrdv
    @15
    @22
    @4
    @9
    f1oeq3
    syl
    mpbiri
    #
    gsumf1o
    wph
    @10
    @11
    cG
    cgsu
    wph
    vz
    @4
    @8
    @0
    cfv
    #
    cmpt
    #
    vk
    vj
    cD
    cE
    @12
    @1
    @0
    co
    #
    cmpt2
    #
    @10
    @11
    vz
    vx
    cD
    @27
    csn
    #
    vk
    @27
    cE
    csb
    #
    cxp
    #
    ciun
    #
    @53
    cmpt
    #
    vx
    vy
    cD
    @58
    @33
    @27
    @0
    co
    #
    cmpt2
    @54
    @56
    vx
    vy
    vz
    cD
    @58
    @53
    @62
    @5
    @34
    wceq
    #
    @53
    @33
    @27
    cop
    #
    @0
    cfv
    @62
    @63
    @8
    @64
    @0
    @63
    @8
    @34
    csn
    #
    ccnv
    #
    cuni
    @64
    @63
    @7
    @66
    @63
    @6
    @65
    @5
    @34
    sneq
    cnveqd
    unieqd
    @27
    @33
    opswap
    syl6eq
    fveq2d
    @33
    @27
    @0
    df-ov
    syl6eqr
    mpt2mptx
    @4
    @60
    wceq
    @54
    @61
    wceq
    vk
    vx
    cD
    @3
    @59
    vx
    @3
    nfcv
    vk
    @57
    @58
    vk
    @57
    nfcv
    vk
    @27
    cE
    nfcsb1v
    #
    nfxp
    vk
    vx
    weq
    #
    @2
    @57
    cE
    @58
    @1
    @27
    sneq
    vk
    @27
    cE
    csbeq1a
    #
    xpeq12d
    cbviun
    vz
    @4
    @60
    @53
    mpteq1
    ax-mp
    vk
    vj
    vx
    vy
    cD
    cE
    @55
    @58
    @62
    vx
    cE
    nfcv
    @67
    vx
    @55
    nfcv
    vy
    @55
    nfcv
    vk
    @33
    @27
    @0
    vk
    @33
    nfcv
    vj
    vk
    cA
    cC
    cX
    nfmpt22
    vk
    @27
    nfcv
    nfov
    vj
    @33
    @27
    @0
    vj
    @33
    nfcv
    vj
    vk
    cA
    cC
    cX
    nfmpt21
    vj
    @27
    nfcv
    nfov
    @69
    @68
    vj
    vy
    weq
    @55
    @12
    @27
    @0
    co
    @62
    @1
    @27
    @12
    @0
    oveq2
    @12
    @33
    @27
    @0
    oveq1
    sylan9eq
    cbvmpt2x
    3eqtr4i
    wph
    vz
    vx
    @4
    @15
    @8
    @27
    @0
    cfv
    @53
    @9
    @0
    wph
    @4
    @15
    @9
    wf
    #
    @8
    @15
    wcel
    vz
    @4
    wral
    wph
    @21
    @70
    @52
    @4
    @15
    @9
    f1of
    syl
    vz
    @4
    @15
    @8
    @9
    @9
    eqid
    fmpt
    sylibr
    wph
    @9
    eqidd
    wph
    vx
    @15
    cB
    @0
    @20
    feqmptd
    @27
    @8
    @0
    fveq2
    fmptcof
    wph
    vk
    vj
    cD
    cE
    cX
    @55
    wph
    @49
    @50
    w3a
    @55
    cX
    wph
    @49
    @50
    @55
    cX
    wceq
    #
    wph
    @51
    @48
    @71
    gsumcom2.c
    wph
    @48
    @18
    @71
    wph
    @48
    @18
    gsum2d2.f
    ex
    @17
    @47
    @18
    @71
    vj
    vk
    cA
    cC
    cX
    @0
    cB
    @19
    ovmpt4g
    3expia
    sylcom
    sylbird
    3impib
    eqcomd
    mpt2eq3dva
    3eqtr4a
    oveq2d
    eqtrd
end
