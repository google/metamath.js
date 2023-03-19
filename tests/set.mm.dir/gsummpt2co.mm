include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "c2nd.mm"
include "cfv.mm"
include "csb.mm"
include "cmpt2.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "wcel.mm"
include "cop.mm"
include "wceq.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "elcnv.mm"
include "vex.mm"
include "op2ndd.mm"
include "adantr.mm"
include "cdm.mm"
include "dmmptss.mm"
include "breldm.mm"
include "sseldi.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "wfun.mm"
include "crn.mm"
include "wreu.mm"
include "funmpt2.mm"
include "funcnvcnv.mm"
include "ax-mp.mm"
include "dfdm4.mm"
include "dmeqi.mm"
include "wral.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "syl.mm"
include "syl5eq.mm"
include "syl5eqr.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "wrel.mm"
include "relcnv.mm"
include "fcnvgreu.mm"
include "mpanl1.mm"
include "syl2anc.mm"
include "gsummptf1o.mm"
include "cxp.mm"
include "ciun.mm"
include "rnmptss.mm"
include "dfcnv2.mm"
include "mpteq1d.mm"
include "nfcv.mm"
include "csbeq1.mm"
include "csbid.mm"
include "syl6eq.mm"
include "mpt2mptxf.mm"
include "oveq2d.mm"
include "cvv.mm"
include "cfn.mm"
include "mptfi.mm"
include "syl5eqel.mm"
include "cnvfi.mm"
include "3syl.mm"
include "imaexg.mm"
include "simpll.mm"
include "imassrn.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "elimasn.mm"
include "biimpi.mm"
include "sylibr.mm"
include "anasss.mm"
include "wn.mm"
include "df-br.mm"
include "pm2.24d.mm"
include "imp.mm"
include "gsum2d2.mm"
include "3eqtrd.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "cbvmpt.mm"
include "oveq2i.mm"
include "syl6eqr.mm"

theorem gsummpt2co
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vz: setvar z
  let vp: setvar p
  assume gsummpt2co.b: |- B = ( Base ` W )
  assume gsummpt2co.z: |- .0. = ( 0g ` W )
  assume gsummpt2co.w: |- ( ph -> W e. CMnd )
  assume gsummpt2co.a: |- ( ph -> A e. Fin )
  assume gsummpt2co.e: |- ( ph -> E e. V )
  assume gsummpt2co.1: |- ( ( ph /\ x e. A ) -> C e. B )
  assume gsummpt2co.2: |- ( ( ph /\ x e. A ) -> D e. E )
  assume gsummpt2co.3: |- F = ( x e. A |-> D )

  disjoint .0. x
  disjoint .0. y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint E x
  disjoint E y
  disjoint F x
  disjoint F y
  disjoint V y
  disjoint W x
  disjoint W y
  disjoint ph x
  disjoint .0. z
  disjoint x z
  disjoint y z
  disjoint A p
  disjoint A z
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint B p
  disjoint B z
  disjoint C p
  disjoint C z
  disjoint E p
  disjoint E z
  disjoint F p
  disjoint F z
  disjoint V z
  disjoint W z
  disjoint p ph
  disjoint ph z
  assert |- ( ph -> ( W gsum ( x e. A |-> C ) ) = ( W gsum ( y e. E |-> ( W gsum ( x e. ( `' F " { y } ) |-> C ) ) ) ) )

  proof
    wph
    cW
    vx
    cA
    cC
    cmpt
    cgsu
    co
    #
    cW
    vz
    cE
    cW
    vx
    cF
    ccnv
    #
    vz
    cv
    #
    csn
    #
    cima
    #
    cC
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cW
    vy
    cE
    cW
    vx
    @1
    vy
    cv
    #
    csn
    #
    cima
    #
    cC
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
    @0
    cW
    vp
    @1
    vx
    vp
    cv
    #
    c2nd
    cfv
    #
    cC
    csb
    #
    cmpt
    #
    cgsu
    co
    cW
    vz
    vx
    cE
    @4
    cC
    cmpt2
    #
    cgsu
    co
    @8
    wph
    vx
    vp
    cA
    cB
    cC
    @1
    @16
    cB
    cW
    @17
    c.0
    vx
    @16
    cC
    nfcsb1v
    #
    gsummpt2co.b
    gsummpt2co.z
    vx
    @16
    cC
    csbeq1a
    gsummpt2co.w
    gsummpt2co.a
    cB
    cB
    wss
    wph
    cB
    ssid
    a1i
    gsummpt2co.1
    @15
    @1
    wcel
    #
    @16
    cA
    wcel
    #
    wph
    @21
    @15
    @2
    vx
    cv
    #
    cop
    #
    wceq
    #
    @23
    @2
    cF
    wbr
    #
    wa
    #
    vx
    wex
    vz
    wex
    @22
    vz
    vx
    @15
    cF
    elcnv
    @27
    @22
    vz
    vx
    @27
    @16
    @23
    cA
    @25
    @16
    @23
    wceq
    #
    @26
    @2
    @23
    @15
    vz
    vex
    #
    vx
    vex
    #
    op2ndd
    #
    adantr
    @26
    @23
    cA
    wcel
    #
    @25
    @26
    cF
    cdm
    #
    cA
    @23
    vx
    cA
    cD
    cF
    gsummpt2co.3
    dmmptss
    #
    @23
    @2
    cF
    @30
    @29
    breldm
    sseldi
    adantl
    eqeltrd
    exlimivv
    sylbi
    adantl
    wph
    @32
    wa
    #
    @1
    ccnv
    wfun
    #
    @23
    @1
    crn
    #
    wcel
    #
    @23
    @16
    wceq
    vp
    @1
    wreu
    #
    @36
    @35
    cF
    wfun
    @36
    vx
    cA
    cD
    cF
    gsummpt2co.3
    funmpt2
    cF
    funcnvcnv
    ax-mp
    a1i
    wph
    @38
    @32
    wph
    @37
    cA
    @23
    wph
    @37
    @33
    cA
    cF
    dfdm4
    #
    wph
    @33
    vx
    cA
    cD
    cmpt
    #
    cdm
    #
    cA
    cF
    @41
    gsummpt2co.3
    dmeqi
    wph
    cD
    cE
    wcel
    #
    vx
    cA
    wral
    #
    @42
    cA
    wceq
    wph
    @43
    vx
    cA
    gsummpt2co.2
    ralrimiva
    #
    vx
    cA
    cD
    cE
    dmmptg
    syl
    syl5eq
    syl5eqr
    eleq2d
    biimpar
    @1
    wrel
    @36
    @38
    @39
    cF
    relcnv
    @1
    @23
    vp
    fcnvgreu
    mpanl1
    syl2anc
    gsummptf1o
    wph
    @18
    @19
    cW
    cgsu
    wph
    @18
    vp
    vz
    cE
    @3
    @4
    cxp
    ciun
    #
    @17
    cmpt
    @19
    wph
    vp
    @1
    @46
    @17
    wph
    cF
    crn
    cE
    wss
    #
    @1
    @46
    wceq
    wph
    @44
    @47
    @45
    vx
    cA
    cD
    cE
    cF
    gsummpt2co.3
    rnmptss
    syl
    vz
    cE
    cF
    dfcnv2
    syl
    mpteq1d
    vz
    vx
    vp
    cE
    @4
    @17
    cC
    vz
    @17
    nfcv
    @20
    @25
    @17
    vx
    @23
    cC
    csb
    #
    cC
    @25
    @28
    @17
    @48
    wceq
    @31
    vx
    @16
    @23
    cC
    csbeq1
    syl
    vx
    cC
    csbid
    syl6eq
    mpt2mptxf
    syl6eq
    oveq2d
    wph
    cE
    cB
    @4
    @1
    vz
    vx
    cW
    cV
    cvv
    cC
    c.0
    gsummpt2co.b
    gsummpt2co.z
    gsummpt2co.w
    gsummpt2co.e
    wph
    @4
    cvv
    wcel
    #
    @2
    cE
    wcel
    #
    wph
    @1
    cfn
    wcel
    #
    @49
    wph
    cA
    cfn
    wcel
    #
    cF
    cfn
    wcel
    @51
    gsummpt2co.a
    @52
    cF
    @41
    cfn
    gsummpt2co.3
    vx
    cA
    cD
    mptfi
    syl5eqel
    cF
    cnvfi
    3syl
    #
    @1
    @3
    cfn
    imaexg
    syl
    adantr
    wph
    @50
    @23
    @4
    wcel
    #
    cC
    cB
    wcel
    #
    wph
    @50
    wa
    #
    @54
    wa
    #
    wph
    @32
    @55
    wph
    @50
    @54
    simpll
    @57
    @4
    cA
    @23
    @4
    @33
    cA
    @4
    @37
    @33
    @1
    @3
    imassrn
    @40
    sseqtr4i
    @34
    sstri
    @57
    @24
    @1
    wcel
    #
    @54
    @54
    @58
    @56
    @54
    @58
    @1
    @2
    @23
    @29
    @30
    elimasn
    #
    biimpi
    adantl
    #
    @59
    sylibr
    sseldi
    gsummpt2co.1
    syl2anc
    anasss
    @53
    wph
    @50
    @54
    wa
    #
    @2
    @23
    @1
    wbr
    #
    wn
    #
    cC
    c.0
    wceq
    #
    wph
    @61
    wa
    #
    @63
    @64
    @65
    @62
    @64
    wph
    @50
    @54
    @62
    @57
    @58
    @62
    @60
    @2
    @23
    @1
    df-br
    sylibr
    anasss
    pm2.24d
    imp
    anasss
    gsum2d2
    3eqtrd
    @14
    @7
    cW
    cgsu
    vy
    vz
    cE
    @13
    @6
    vz
    @13
    nfcv
    vy
    @6
    nfcv
    @9
    @2
    wceq
    #
    @12
    @5
    cW
    cgsu
    @66
    vx
    @11
    @4
    cC
    @66
    @10
    @3
    @1
    @9
    @2
    sneq
    imaeq2d
    mpteq1d
    oveq2d
    cbvmpt
    oveq2i
    syl6eqr
end
