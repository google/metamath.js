include "csmblfn.mm"
include "cfv.mm"
include "wcel.mm"
include "cuni.mm"
include "wss.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "crest.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "cpm.mm"
include "ccnv.mm"
include "cmnf.mm"
include "cioo.mm"
include "cima.mm"
include "cdm.mm"
include "simpr.mm"
include "wceq.mm"
include "csalg.mm"
include "cvv.mm"
include "cmpt.mm"
include "df-smblfn.mm"
include "a1i.mm"
include "unieq.mm"
include "oveq2d.mm"
include "rabeqd.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "ralbidv.mm"
include "rabbidv.mm"
include "eqtrd.mm"
include "adantl.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmptd.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "elrabi.mm"
include "syl.mm"
include "elpmi2.mm"
include "syl5eqss.mm"
include "syldan.mm"
include "elpmi.mm"
include "simpld.mm"
include "wb.mm"
include "feq2i.mm"
include "mpbird.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "dmeq.mm"
include "eleq12d.mm"
include "elrab.mm"
include "simprbi.mm"
include "rspa.mm"
include "syl2anc.mm"
include "simpl.mm"
include "rexrd.mm"
include "preimaioomnf.mm"
include "eqcomd.mm"
include "oveq2i.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "ex.mm"
include "reex.mm"
include "uniexd.mm"
include "simprr.mm"
include "cxp.mm"
include "fssxp.mm"
include "xpss1.mm"
include "sstrd.mm"
include "dmss.mm"
include "dmxpss.mm"
include "elpm2r.mm"
include "syl22anc.mm"
include "3adantr3.mm"
include "ralbidva.mm"
include "biimpd.mm"
include "imp.mm"
include "3adantr1.mm"
include "jca.mm"
include "sylibr.mm"
include "impbid.mm"

theorem issmflem
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cS: class S
  let cF: class F
  let va: setvar a
  let vf: setvar f
  let vs: setvar s
  let vk: setvar k
  assume issmflem.s: |- ( ph -> S e. SAlg )
  assume issmflem.d: |- D = dom F

  disjoint D a
  disjoint D x
  disjoint a x
  disjoint F a
  disjoint F x
  disjoint S a
  disjoint S x
  disjoint a ph
  disjoint ph x
  disjoint F f
  disjoint a f
  disjoint S f
  disjoint S s
  disjoint a s
  disjoint f s
  disjoint ph s
  disjoint k x
  assert |- ( ph -> ( F e. ( SMblFn ` S ) <-> ( D C_ U. S /\ F : D --> RR /\ A. a e. RR { x e. D | ( F ` x ) < a } e. ( S |`t D ) ) ) )

  proof
    wph
    cF
    cS
    csmblfn
    cfv
    #
    wcel
    #
    cD
    cS
    cuni
    #
    wss
    #
    cD
    cr
    cF
    wf
    #
    vx
    cv
    cF
    cfv
    va
    cv
    #
    clt
    wbr
    vx
    cD
    crab
    #
    cS
    cD
    crest
    co
    #
    wcel
    #
    va
    cr
    wral
    #
    w3a
    #
    wph
    @1
    @10
    wph
    @1
    wa
    #
    @3
    @4
    @9
    wph
    @1
    cF
    cr
    @2
    cpm
    co
    #
    wcel
    #
    @3
    @11
    cF
    vf
    cv
    #
    ccnv
    #
    cmnf
    @5
    cioo
    co
    #
    cima
    #
    cS
    @14
    cdm
    #
    crest
    co
    #
    wcel
    #
    va
    cr
    wral
    #
    vf
    @12
    crab
    #
    wcel
    #
    @13
    @11
    cF
    @0
    @22
    wph
    @1
    simpr
    wph
    @0
    @22
    wceq
    @1
    wph
    vs
    cS
    @17
    vs
    cv
    #
    @18
    crest
    co
    #
    wcel
    #
    va
    cr
    wral
    #
    vf
    cr
    @24
    cuni
    #
    cpm
    co
    #
    crab
    #
    @22
    csalg
    csmblfn
    cvv
    csmblfn
    vs
    csalg
    @30
    cmpt
    wceq
    wph
    vf
    vs
    va
    df-smblfn
    a1i
    @24
    cS
    wceq
    #
    @30
    @22
    wceq
    wph
    @31
    @30
    @27
    vf
    @12
    crab
    @22
    @31
    @27
    vf
    @29
    @12
    @31
    @28
    @2
    cr
    cpm
    @24
    cS
    unieq
    oveq2d
    rabeqd
    @31
    @27
    @21
    vf
    @12
    @31
    @26
    @20
    va
    cr
    @31
    @25
    @19
    @17
    @24
    cS
    @18
    crest
    oveq1
    eleq2d
    ralbidv
    rabbidv
    eqtrd
    adantl
    issmflem.s
    @22
    cvv
    wcel
    wph
    @21
    vf
    @12
    cr
    @2
    cpm
    ovex
    rabex
    a1i
    fvmptd
    #
    adantr
    eleqtrd
    #
    @21
    vf
    cF
    @12
    elrabi
    syl
    #
    @13
    @3
    wph
    @13
    cD
    cF
    cdm
    #
    @2
    issmflem.d
    cr
    @2
    cF
    elpmi2
    syl5eqss
    adantl
    syldan
    @11
    @4
    @35
    cr
    cF
    wf
    #
    @11
    @36
    @35
    @2
    wss
    #
    @11
    @13
    @36
    @37
    wa
    @34
    cr
    @2
    cF
    elpmi
    syl
    simpld
    @4
    @36
    wb
    @11
    cD
    @35
    cr
    cF
    issmflem.d
    feq2i
    a1i
    mpbird
    #
    @11
    @8
    va
    cr
    @11
    @5
    cr
    wcel
    #
    wa
    #
    @8
    cF
    ccnv
    #
    @16
    cima
    #
    cS
    @35
    crest
    co
    #
    wcel
    #
    @40
    @44
    va
    cr
    wral
    #
    @39
    @44
    @11
    @45
    @39
    @11
    @23
    @45
    @33
    @23
    @13
    @45
    @21
    @45
    vf
    cF
    @12
    @14
    cF
    wceq
    #
    @20
    @44
    va
    cr
    @46
    @17
    @42
    @19
    @43
    @46
    @15
    @41
    @16
    @14
    cF
    cnveq
    imaeq1d
    @46
    @18
    @35
    cS
    crest
    @14
    cF
    dmeq
    oveq2d
    eleq12d
    ralbidv
    elrab
    #
    simprbi
    syl
    adantr
    @11
    @39
    simpr
    #
    @44
    va
    cr
    rspa
    syl2anc
    @40
    @6
    @42
    @7
    @43
    @40
    @4
    @39
    @6
    @42
    wceq
    @11
    @4
    @39
    @38
    adantr
    @48
    @4
    @39
    wa
    #
    @42
    @6
    @49
    vx
    cD
    @5
    cF
    @4
    @39
    simpl
    @49
    @5
    @4
    @39
    simpr
    rexrd
    preimaioomnf
    eqcomd
    #
    syl2anc
    @7
    @43
    wceq
    @40
    cD
    @35
    cS
    crest
    issmflem.d
    oveq2i
    a1i
    eleq12d
    mpbird
    ralrimiva
    3jca
    ex
    wph
    @10
    @1
    wph
    @10
    wa
    #
    cF
    @22
    @0
    @51
    @13
    @45
    wa
    @23
    @51
    @13
    @45
    wph
    @3
    @4
    @13
    @9
    wph
    @3
    @4
    wa
    #
    wa
    #
    cr
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    @4
    @3
    @13
    @54
    @53
    reex
    a1i
    wph
    @55
    @52
    wph
    cS
    csalg
    issmflem.s
    uniexd
    adantr
    wph
    @3
    @4
    simprr
    wph
    @52
    cF
    @2
    cr
    cxp
    #
    wss
    #
    @3
    @52
    @57
    wph
    @52
    cF
    cD
    cr
    cxp
    #
    @56
    @4
    cF
    @58
    wss
    @3
    cD
    cr
    cF
    fssxp
    adantl
    @3
    @58
    @56
    wss
    @4
    cD
    @2
    cr
    xpss1
    adantr
    sstrd
    adantl
    wph
    @57
    wa
    cD
    @35
    @2
    issmflem.d
    @57
    @37
    wph
    @57
    @35
    @56
    cdm
    #
    @2
    cF
    @56
    dmss
    @59
    @2
    wss
    @57
    @2
    cr
    dmxpss
    a1i
    sstrd
    adantl
    syl5eqss
    syldan
    cr
    @2
    cD
    cF
    cvv
    cvv
    elpm2r
    syl22anc
    3adantr3
    wph
    @4
    @9
    @45
    @3
    @4
    @9
    wa
    @45
    wph
    @4
    @9
    @45
    @4
    @9
    @45
    @4
    @8
    @44
    va
    cr
    @49
    @6
    @42
    @7
    @43
    @50
    @49
    cD
    @35
    cS
    crest
    cD
    @35
    wceq
    @49
    issmflem.d
    a1i
    oveq2d
    eleq12d
    ralbidva
    biimpd
    imp
    adantl
    3adantr1
    jca
    @47
    sylibr
    wph
    @22
    @0
    wceq
    @10
    wph
    @0
    @22
    @32
    eqcomd
    adantr
    eleqtrd
    ex
    impbid
end
