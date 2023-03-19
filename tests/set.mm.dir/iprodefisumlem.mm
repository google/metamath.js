include "cmul.mm"
include "ce.mm"
include "ccom.mm"
include "cseq.mm"
include "caddc.mm"
include "cc.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "fvco3.mm"
include "sylan.mm"
include "ffvelrnda.mm"
include "efcl.mm"
include "syl.mm"
include "eqeltrd.mm"
include "prodf.mm"
include "ffn.mm"
include "eff.mm"
include "ax-mp.mm"
include "serf.mm"
include "fnfco.mm"
include "sylancr.mm"
include "wi.mm"
include "cuz.mm"
include "c1.mm"
include "co.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cz.mm"
include "uzid.mm"
include "syl6eleqr.mm"
include "syl2anc.mm"
include "seq1.mm"
include "3eqtr4d.mm"
include "a1i.mm"
include "w3a.mm"
include "oveq1.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "peano2uz.mm"
include "adantr.mm"
include "oveq2d.mm"
include "expcom.mm"
include "eqcomi.mm"
include "eleq2s.mm"
include "imp.mm"
include "ffvelrnd.mm"
include "efadd.mm"
include "eqtr4d.mm"
include "3adant3.mm"
include "eqtrd.mm"
include "seqp1.mm"
include "3exp.mm"
include "a2d.mm"
include "uzind4.mm"
include "impcom.mm"
include "eqfnfvd.mm"

theorem iprodefisumlem
  let wph: wff ph
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  assume iprodefisumlem.1: |- Z = ( ZZ>= ` M )
  assume iprodefisumlem.2: |- ( ph -> M e. ZZ )
  assume iprodefisumlem.3: |- ( ph -> F : Z --> CC )


  assert |- ( ph -> seq M ( x. , ( exp o. F ) ) = ( exp o. seq M ( + , F ) ) )

  proof
    wph
    vk
    cZ
    cmul
    ce
    cF
    ccom
    #
    cM
    cseq
    #
    ce
    caddc
    cF
    cM
    cseq
    #
    ccom
    #
    wph
    cZ
    cc
    @1
    wf
    @1
    cZ
    wfn
    wph
    vk
    @0
    cM
    cZ
    iprodefisumlem.1
    iprodefisumlem.2
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @4
    @0
    cfv
    #
    @4
    cF
    cfv
    #
    ce
    cfv
    #
    cc
    wph
    cZ
    cc
    cF
    wf
    #
    @5
    @7
    @9
    wceq
    iprodefisumlem.3
    cZ
    cc
    @4
    ce
    cF
    fvco3
    sylan
    @6
    @8
    cc
    wcel
    @9
    cc
    wcel
    wph
    cZ
    cc
    @4
    cF
    iprodefisumlem.3
    ffvelrnda
    #
    @8
    efcl
    syl
    eqeltrd
    prodf
    cZ
    cc
    @1
    ffn
    syl
    wph
    ce
    cc
    wfn
    #
    cZ
    cc
    @2
    wf
    #
    @3
    cZ
    wfn
    cc
    cc
    ce
    wf
    @12
    eff
    cc
    cc
    ce
    ffn
    ax-mp
    wph
    vk
    cF
    cM
    cZ
    iprodefisumlem.1
    iprodefisumlem.2
    @11
    serf
    #
    cc
    cZ
    ce
    @2
    fnfco
    sylancr
    @6
    @4
    @1
    cfv
    #
    @4
    @2
    cfv
    #
    ce
    cfv
    #
    @4
    @3
    cfv
    #
    @5
    wph
    @15
    @17
    wceq
    #
    wph
    @19
    wi
    #
    @4
    cM
    cuz
    cfv
    #
    cZ
    wph
    vj
    cv
    #
    @1
    cfv
    #
    @22
    @2
    cfv
    #
    ce
    cfv
    #
    wceq
    #
    wi
    wph
    cM
    @1
    cfv
    #
    cM
    @2
    cfv
    #
    ce
    cfv
    #
    wceq
    #
    wi
    #
    wph
    vn
    cv
    #
    @1
    cfv
    #
    @32
    @2
    cfv
    #
    ce
    cfv
    #
    wceq
    #
    wi
    wph
    @32
    c1
    caddc
    co
    #
    @1
    cfv
    #
    @37
    @2
    cfv
    #
    ce
    cfv
    #
    wceq
    #
    wi
    @20
    vj
    vn
    cM
    @4
    @22
    cM
    wceq
    #
    @26
    @30
    wph
    @42
    @23
    @27
    @25
    @29
    @22
    cM
    @1
    fveq2
    @42
    @24
    @28
    ce
    @22
    cM
    @2
    fveq2
    fveq2d
    eqeq12d
    imbi2d
    vj
    vn
    weq
    #
    @26
    @36
    wph
    @43
    @23
    @33
    @25
    @35
    @22
    @32
    @1
    fveq2
    @43
    @24
    @34
    ce
    @22
    @32
    @2
    fveq2
    fveq2d
    eqeq12d
    imbi2d
    @22
    @37
    wceq
    #
    @26
    @41
    wph
    @44
    @23
    @38
    @25
    @40
    @22
    @37
    @1
    fveq2
    @44
    @24
    @39
    ce
    @22
    @37
    @2
    fveq2
    fveq2d
    eqeq12d
    imbi2d
    vj
    vk
    weq
    #
    @26
    @19
    wph
    @45
    @23
    @15
    @25
    @17
    @22
    @4
    @1
    fveq2
    @45
    @24
    @16
    ce
    @22
    @4
    @2
    fveq2
    fveq2d
    eqeq12d
    imbi2d
    @31
    cM
    cz
    wcel
    #
    wph
    cM
    @0
    cfv
    #
    cM
    cF
    cfv
    #
    ce
    cfv
    #
    @27
    @29
    wph
    @10
    cM
    cZ
    wcel
    @47
    @49
    wceq
    iprodefisumlem.3
    wph
    cM
    @21
    cZ
    wph
    @46
    cM
    @21
    wcel
    iprodefisumlem.2
    cM
    uzid
    syl
    iprodefisumlem.1
    syl6eleqr
    cZ
    cc
    cM
    ce
    cF
    fvco3
    syl2anc
    wph
    @46
    @27
    @47
    wceq
    iprodefisumlem.2
    cmul
    @0
    cM
    seq1
    syl
    wph
    @28
    @48
    ce
    wph
    @46
    @28
    @48
    wceq
    iprodefisumlem.2
    caddc
    cF
    cM
    seq1
    syl
    fveq2d
    3eqtr4d
    a1i
    @32
    @21
    wcel
    #
    wph
    @36
    @41
    @50
    wph
    @36
    @41
    @50
    wph
    @36
    w3a
    #
    @33
    @37
    @0
    cfv
    #
    cmul
    co
    #
    @34
    @37
    cF
    cfv
    #
    caddc
    co
    #
    ce
    cfv
    #
    @38
    @40
    @51
    @53
    @35
    @52
    cmul
    co
    #
    @56
    @36
    @50
    @53
    @57
    wceq
    wph
    @33
    @35
    @52
    cmul
    oveq1
    3ad2ant3
    @50
    wph
    @57
    @56
    wceq
    @36
    @50
    wph
    wa
    #
    @57
    @35
    @54
    ce
    cfv
    #
    cmul
    co
    #
    @56
    @58
    @52
    @59
    @35
    cmul
    @58
    @10
    @37
    cZ
    wcel
    #
    @52
    @59
    wceq
    wph
    @10
    @50
    iprodefisumlem.3
    adantl
    #
    @50
    @61
    wph
    @50
    @37
    @21
    cZ
    cM
    @32
    peano2uz
    iprodefisumlem.1
    syl6eleqr
    adantr
    #
    cZ
    cc
    @37
    ce
    cF
    fvco3
    syl2anc
    oveq2d
    @58
    @34
    cc
    wcel
    #
    @54
    cc
    wcel
    @56
    @60
    wceq
    @50
    wph
    @64
    wph
    @64
    wi
    @32
    cZ
    @21
    wph
    @32
    cZ
    wcel
    @64
    wph
    cZ
    cc
    @32
    @2
    @14
    ffvelrnda
    expcom
    cZ
    @21
    iprodefisumlem.1
    eqcomi
    eleq2s
    imp
    @58
    cZ
    cc
    @37
    cF
    @62
    @63
    ffvelrnd
    @34
    @54
    efadd
    syl2anc
    eqtr4d
    3adant3
    eqtrd
    @50
    wph
    @38
    @53
    wceq
    #
    @36
    @50
    @65
    wph
    cmul
    @0
    cM
    @32
    seqp1
    adantr
    3adant3
    @50
    wph
    @40
    @56
    wceq
    @36
    @58
    @39
    @55
    ce
    @50
    @39
    @55
    wceq
    wph
    caddc
    cF
    cM
    @32
    seqp1
    adantr
    fveq2d
    3adant3
    3eqtr4d
    3exp
    a2d
    uzind4
    iprodefisumlem.1
    eleq2s
    impcom
    wph
    @13
    @5
    @18
    @17
    wceq
    @14
    cZ
    cc
    @4
    ce
    @2
    fvco3
    sylan
    eqtr4d
    eqfnfvd
end
