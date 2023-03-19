include "cn0.mm"
include "csseq.mm"
include "co.mm"
include "wf.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "cuz.mm"
include "cun.mm"
include "clsw.mm"
include "cvv.mm"
include "cv.mm"
include "cs1.mm"
include "cconcat.mm"
include "cmpt2.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "ccom.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cword.mm"
include "wcel.mm"
include "wrdf.mm"
include "syl.mm"
include "cdif.mm"
include "cres.mm"
include "cdm.mm"
include "wa.mm"
include "wral.mm"
include "vex.mm"
include "a1i.mm"
include "c1.mm"
include "cmin.mm"
include "fvex.mm"
include "df-lsw.mm"
include "dmmpti.mm"
include "syl6eleqr.mm"
include "wne.mm"
include "eldifsn.mm"
include "ccnv.mm"
include "cima.mm"
include "inss1.mm"
include "eqsstri.mm"
include "sseli.mm"
include "lswcl.mm"
include "sylan.mm"
include "sylbi.mm"
include "adantl.mm"
include "jca.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "wfun.mm"
include "wb.mm"
include "fnmpti.mm"
include "fnfun.mm"
include "ffvresb.mm"
include "mp2b.mm"
include "sylibr.mm"
include "eqid.mm"
include "cz.mm"
include "lencl.mm"
include "nn0zd.mm"
include "ovex.mm"
include "simpr.mm"
include "adantr.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "uztrn.mm"
include "syl2anc.mm"
include "nn0uz.mm"
include "fvconst2g.mm"
include "sylancr.mm"
include "sseqmw.mm"
include "ffvelrnd.mm"
include "s1cld.mm"
include "ccatcl.mm"
include "caddc.mm"
include "ccatws1len.mm"
include "uzid.mm"
include "peano2uz.mm"
include "3syl.mm"
include "eqeltrd.mm"
include "cpnf.mm"
include "hashf.mm"
include "ffn.mm"
include "elpreima.mm"
include "sylanbrc.mm"
include "elind.mm"
include "ccatws1n0.mm"
include "eqidd.mm"
include "simprl.mm"
include "fveq2d.mm"
include "s1eqd.mm"
include "oveq12d.mm"
include "ovmpt2d.mm"
include "eldifi.mm"
include "ad2antrl.mm"
include "sseldi.mm"
include "syl6eleq.mm"
include "elin2d.mm"
include "simpl2im.mm"
include "seqf.mm"
include "fco2.mm"
include "fzouzdisj.mm"
include "fun.mm"
include "syl21anc.mm"
include "sseqval.mm"
include "fzouzsplit.mm"
include "syl5eq.mm"
include "unidm.mm"
include "eqcomd.mm"
include "feq123d.mm"
include "mpbird.mm"

theorem sseqf
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cM: class M
  let cW: class W
  let vf: setvar f
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  assume sseqval.1: |- ( ph -> S e. _V )
  assume sseqval.2: |- ( ph -> M e. Word S )
  assume sseqval.3: |- W = ( Word S i^i ( `' # " ( ZZ>= ` ( # ` M ) ) ) )
  assume sseqval.4: |- ( ph -> F : W --> S )


  assert |- ( ph -> ( M seqstr F ) : NN0 --> S )

  proof
    wph
    cn0
    cS
    cM
    cF
    csseq
    co
    #
    wf
    cc0
    cM
    chash
    cfv
    #
    cfzo
    co
    #
    @1
    cuz
    cfv
    #
    cun
    #
    cS
    cS
    cun
    #
    cM
    clsw
    vx
    vy
    cvv
    cvv
    vx
    cv
    #
    @6
    cF
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    cmpt2
    #
    cn0
    cM
    cM
    cF
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    csn
    cxp
    #
    @1
    cseq
    #
    ccom
    #
    cun
    #
    wf
    #
    wph
    @2
    cS
    cM
    wf
    #
    @3
    cS
    @16
    wf
    #
    @2
    @3
    cin
    c0
    wceq
    #
    @18
    wph
    cM
    cS
    cword
    #
    wcel
    #
    @19
    sseqval.2
    cS
    cM
    wrdf
    syl
    wph
    cW
    c0
    csn
    #
    cdif
    #
    cS
    clsw
    @25
    cres
    wf
    #
    @3
    @25
    @15
    wf
    @20
    wph
    vw
    cv
    #
    clsw
    cdm
    #
    wcel
    #
    @27
    clsw
    cfv
    cS
    wcel
    #
    wa
    #
    vw
    @25
    wral
    #
    @26
    wph
    @31
    vw
    @25
    wph
    @27
    @25
    wcel
    #
    wa
    #
    @29
    @30
    @34
    @27
    cvv
    @28
    @27
    cvv
    wcel
    @34
    vw
    vex
    a1i
    vx
    cvv
    @6
    chash
    cfv
    c1
    cmin
    co
    #
    @6
    cfv
    #
    clsw
    @35
    @6
    fvex
    #
    vx
    df-lsw
    #
    dmmpti
    syl6eleqr
    @33
    @30
    wph
    @33
    @27
    cW
    wcel
    #
    @27
    c0
    wne
    #
    wa
    @30
    @27
    cW
    c0
    eldifsn
    @39
    @27
    @22
    wcel
    @40
    @30
    cW
    @22
    @27
    cW
    @22
    chash
    ccnv
    @3
    cima
    #
    cin
    #
    @22
    sseqval.3
    @22
    @41
    inss1
    eqsstri
    #
    sseli
    cS
    @27
    lswcl
    sylan
    sylbi
    adantl
    jca
    ralrimiva
    clsw
    cvv
    wfn
    clsw
    wfun
    @26
    @32
    wb
    vx
    cvv
    @36
    clsw
    @37
    @38
    fnmpti
    cvv
    clsw
    fnfun
    vw
    @25
    cS
    clsw
    ffvresb
    mp2b
    sylibr
    wph
    va
    vb
    @10
    @25
    @14
    @1
    @3
    @3
    eqid
    wph
    @23
    @1
    cz
    wcel
    #
    sseqval.2
    @23
    @1
    cS
    cM
    lencl
    #
    nn0zd
    syl
    #
    wph
    va
    cv
    #
    @3
    wcel
    #
    wa
    #
    @47
    @14
    cfv
    #
    @13
    @25
    @49
    @13
    cvv
    wcel
    #
    @47
    cn0
    wcel
    @50
    @13
    wceq
    cM
    @12
    cconcat
    ovex
    #
    @49
    @47
    cc0
    cuz
    cfv
    #
    cn0
    @49
    @48
    @1
    @53
    wcel
    #
    @47
    @53
    wcel
    wph
    @48
    simpr
    @49
    @1
    cn0
    wcel
    #
    @54
    wph
    @55
    @48
    wph
    @23
    @55
    sseqval.2
    @45
    syl
    adantr
    @1
    elnn0uz
    #
    sylib
    @1
    @47
    cc0
    uztrn
    syl2anc
    nn0uz
    syl6eleqr
    cn0
    @13
    @47
    cvv
    fvconst2g
    sylancr
    @49
    @13
    cW
    wcel
    #
    @13
    c0
    wne
    #
    @13
    @25
    wcel
    wph
    @57
    @48
    wph
    @13
    @42
    cW
    wph
    @22
    @41
    @13
    wph
    @23
    @12
    @22
    wcel
    @13
    @22
    wcel
    sseqval.2
    wph
    @11
    cS
    wph
    cW
    cS
    cM
    cF
    sseqval.4
    wph
    cS
    cF
    cM
    cW
    sseqval.1
    sseqval.2
    sseqval.3
    sseqval.4
    sseqmw
    ffvelrnd
    s1cld
    cS
    cM
    @12
    ccatcl
    syl2anc
    wph
    @51
    @13
    chash
    cfv
    #
    @3
    wcel
    #
    @13
    @41
    wcel
    #
    @51
    wph
    @52
    a1i
    wph
    @59
    @1
    c1
    caddc
    co
    #
    @3
    wph
    @23
    @59
    @62
    wceq
    sseqval.2
    cS
    cM
    @11
    ccatws1len
    syl
    wph
    @44
    @1
    @3
    wcel
    @62
    @3
    wcel
    @46
    @1
    uzid
    @1
    @1
    peano2uz
    3syl
    eqeltrd
    cvv
    cn0
    cpnf
    csn
    cun
    #
    chash
    wf
    #
    chash
    cvv
    wfn
    #
    @61
    @51
    @60
    wa
    wb
    hashf
    cvv
    @63
    chash
    ffn
    #
    cvv
    @13
    @3
    chash
    elpreima
    mp2b
    sylanbrc
    elind
    sseqval.3
    syl6eleqr
    adantr
    wph
    @58
    @48
    wph
    @23
    @58
    sseqval.2
    cS
    cM
    @11
    ccatws1n0
    syl
    adantr
    @13
    cW
    c0
    eldifsn
    sylanbrc
    eqeltrd
    wph
    @47
    @25
    wcel
    #
    vb
    cv
    #
    @25
    wcel
    #
    wa
    #
    wa
    #
    @47
    @68
    @10
    co
    @47
    @47
    cF
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    @25
    @71
    vx
    vy
    @47
    @68
    cvv
    cvv
    @9
    @74
    @10
    cvv
    @71
    @10
    eqidd
    @71
    @6
    @47
    wceq
    #
    vy
    cv
    @68
    wceq
    #
    wa
    wa
    #
    @6
    @47
    @8
    @73
    cconcat
    @71
    @75
    @76
    simprl
    #
    @77
    @7
    @72
    @77
    @6
    @47
    cF
    @78
    fveq2d
    s1eqd
    oveq12d
    @47
    cvv
    wcel
    #
    @71
    va
    vex
    a1i
    @68
    cvv
    wcel
    @71
    vb
    vex
    a1i
    @74
    cvv
    wcel
    #
    @71
    @47
    @73
    cconcat
    ovex
    a1i
    #
    ovmpt2d
    @71
    @74
    cW
    wcel
    @74
    c0
    wne
    #
    @74
    @25
    wcel
    @71
    @74
    @42
    cW
    @71
    @22
    @41
    @74
    @71
    @47
    @22
    wcel
    #
    @73
    @22
    wcel
    @74
    @22
    wcel
    @71
    cW
    @22
    @47
    @43
    @67
    @47
    cW
    wcel
    wph
    @69
    @47
    cW
    @24
    eldifi
    #
    ad2antrl
    #
    sseldi
    @71
    @72
    cS
    @71
    cW
    cS
    @47
    cF
    wph
    cW
    cS
    cF
    wf
    @70
    sseqval.4
    adantr
    @85
    ffvelrnd
    s1cld
    cS
    @47
    @73
    ccatcl
    syl2anc
    @71
    @80
    @74
    chash
    cfv
    #
    @3
    wcel
    #
    @74
    @41
    wcel
    #
    @81
    @71
    @86
    @47
    chash
    cfv
    #
    c1
    caddc
    co
    #
    @3
    @71
    @83
    @86
    @90
    wceq
    @67
    @83
    wph
    @69
    @67
    cW
    @22
    @47
    @43
    @84
    sseldi
    ad2antrl
    #
    cS
    @47
    @72
    ccatws1len
    syl
    @71
    @79
    @89
    @3
    wcel
    #
    @90
    @3
    wcel
    @71
    @47
    @41
    wcel
    #
    @79
    @92
    wa
    #
    @71
    @22
    @41
    @47
    @71
    @47
    cW
    @42
    @85
    sseqval.3
    syl6eleq
    elin2d
    @64
    @65
    @93
    @94
    wb
    hashf
    @66
    cvv
    @47
    @3
    chash
    elpreima
    mp2b
    sylib
    @1
    @89
    peano2uz
    simpl2im
    eqeltrd
    @64
    @65
    @88
    @80
    @87
    wa
    wb
    hashf
    @66
    cvv
    @74
    @3
    chash
    elpreima
    mp2b
    sylanbrc
    elind
    sseqval.3
    syl6eleqr
    @71
    @83
    @82
    @91
    cS
    @47
    @72
    ccatws1n0
    syl
    @74
    cW
    c0
    eldifsn
    sylanbrc
    eqeltrd
    seqf
    @3
    @25
    cS
    clsw
    @15
    fco2
    syl2anc
    @21
    wph
    cc0
    @1
    fzouzdisj
    a1i
    @2
    @3
    cS
    cS
    cM
    @16
    fun
    syl21anc
    wph
    cn0
    @4
    cS
    @5
    @0
    @17
    wph
    vx
    vy
    cS
    cF
    cM
    cW
    sseqval.1
    sseqval.2
    sseqval.3
    sseqval.4
    sseqval
    wph
    cn0
    @53
    @4
    nn0uz
    wph
    @23
    @55
    @53
    @4
    wceq
    #
    sseqval.2
    @45
    @55
    @54
    @95
    @56
    cc0
    @1
    fzouzsplit
    sylbi
    3syl
    syl5eq
    wph
    @5
    cS
    @5
    cS
    wceq
    wph
    cS
    unidm
    a1i
    eqcomd
    feq123d
    mpbird
end
