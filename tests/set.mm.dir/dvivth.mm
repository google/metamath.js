include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "cdv.mm"
include "co.mm"
include "cfv.mm"
include "cicc.mm"
include "crn.mm"
include "wss.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "cioo.mm"
include "wrex.mm"
include "cneg.mm"
include "cmpt.mm"
include "cmul.mm"
include "cmin.mm"
include "adantr.mm"
include "ccncf.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "renegcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "cc.mm"
include "wb.mm"
include "ax-resscn.mm"
include "ssid.mm"
include "cncfss.mm"
include "mp2an.mm"
include "sseldi.mm"
include "negfcncf.mm"
include "cncffvrn.mm"
include "sylancr.mm"
include "mpbird.mm"
include "cdm.mm"
include "cvv.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "a1i.mm"
include "recnd.mm"
include "fvexd.mm"
include "feqmptd.mm"
include "oveq2d.mm"
include "ioossre.mm"
include "dvfre.mm"
include "sylancl.mm"
include "feq2d.mm"
include "mpbid.mm"
include "eqtr3d.mm"
include "dvmptneg.mm"
include "dmeqd.mm"
include "dmmptg.mm"
include "negex.mm"
include "mprg.mm"
include "syl6eq.mm"
include "simprl.mm"
include "simprr.mm"
include "ffvelrnd.mm"
include "eleqtrrd.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "iccneg.mm"
include "syl3anc.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "negeqd.mm"
include "fvmpt.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "dvivthlem2.mm"
include "rneqd.mm"
include "eleqtrd.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "sylib.mm"
include "dvmptcl.mm"
include "neg11ad.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "rexbidva.mm"
include "wfn.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "expr.mm"
include "ssrdv.mm"
include "csn.mm"
include "oveq1d.mm"
include "cxr.mm"
include "rexrd.mm"
include "iccid.mm"
include "sylan9eqr.mm"
include "fnfvelrn.mm"
include "snssd.mm"
include "eqsstrd.mm"
include "lttri4d.mm"
include "mpjao3dan.mm"

theorem dvivth
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cM: class M
  let cN: class N
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cC: class C
  assume dvivth.1: |- ( ph -> M e. ( A (,) B ) )
  assume dvivth.2: |- ( ph -> N e. ( A (,) B ) )
  assume dvivth.3: |- ( ph -> F e. ( ( A (,) B ) -cn-> RR ) )
  assume dvivth.4: |- ( ph -> dom ( RR _D F ) = ( A (,) B ) )


  assert |- ( ph -> ( ( ( RR _D F ) ` M ) [,] ( ( RR _D F ) ` N ) ) C_ ran ( RR _D F ) )

  proof
    wph
    cM
    cN
    clt
    wbr
    #
    cM
    cr
    cF
    cdv
    co
    #
    cfv
    #
    cN
    @1
    cfv
    #
    cicc
    co
    #
    @1
    crn
    #
    wss
    cM
    cN
    wceq
    #
    cN
    cM
    clt
    wbr
    #
    wph
    @0
    wa
    vx
    @4
    @5
    wph
    @0
    vx
    cv
    #
    @4
    wcel
    #
    @8
    @5
    wcel
    #
    wph
    @0
    @9
    wa
    #
    wa
    #
    @10
    vw
    cv
    #
    @1
    cfv
    #
    @8
    wceq
    #
    vw
    cA
    cB
    cioo
    co
    #
    wrex
    #
    @12
    @8
    cneg
    #
    @14
    cneg
    #
    wceq
    #
    vw
    @16
    wrex
    #
    @17
    @12
    @18
    vw
    @16
    @19
    cmpt
    #
    crn
    #
    wcel
    #
    @21
    @12
    @18
    cr
    vw
    @16
    @13
    cF
    cfv
    #
    cneg
    #
    cmpt
    #
    cdv
    co
    #
    crn
    @23
    @12
    vy
    cA
    cB
    @18
    @27
    vy
    @16
    vy
    cv
    #
    @27
    cfv
    @18
    @29
    cmul
    co
    cmin
    co
    cmpt
    #
    cM
    cN
    wph
    cM
    @16
    wcel
    #
    @11
    dvivth.1
    adantr
    #
    wph
    cN
    @16
    wcel
    #
    @11
    dvivth.2
    adantr
    #
    wph
    @27
    @16
    cr
    ccncf
    co
    #
    wcel
    #
    @11
    wph
    @36
    @16
    cr
    @27
    wf
    #
    wph
    vw
    @16
    @26
    cr
    @27
    wph
    @13
    @16
    wcel
    #
    wa
    @25
    wph
    @16
    cr
    @13
    cF
    wph
    cF
    @35
    wcel
    #
    @16
    cr
    cF
    wf
    #
    dvivth.3
    @16
    cr
    cF
    cncff
    syl
    #
    ffvelrnda
    renegcld
    @27
    eqid
    #
    fmptd
    wph
    cr
    cc
    wss
    #
    @27
    @16
    cc
    ccncf
    co
    #
    wcel
    #
    @36
    @37
    wb
    ax-resscn
    wph
    cF
    @44
    wcel
    @45
    wph
    @35
    @44
    cF
    @43
    cc
    cc
    wss
    @35
    @44
    wss
    ax-resscn
    cc
    ssid
    @16
    cr
    cc
    cncfss
    mp2an
    dvivth.3
    sseldi
    vw
    @16
    cF
    @27
    @42
    negfcncf
    syl
    @16
    cc
    cr
    @27
    cncffvrn
    sylancr
    mpbird
    adantr
    @12
    @28
    cdm
    @22
    cdm
    #
    @16
    @12
    @28
    @22
    @12
    vw
    @25
    @14
    cr
    cvv
    @16
    cr
    cr
    cc
    cpr
    wcel
    @12
    reelprrecn
    a1i
    #
    @12
    @38
    wa
    #
    @25
    @12
    @16
    cr
    @13
    cF
    wph
    @40
    @11
    @41
    adantr
    #
    ffvelrnda
    recnd
    #
    @48
    @13
    @1
    fvexd
    #
    @12
    @1
    cr
    vw
    @16
    @25
    cmpt
    #
    cdv
    co
    vw
    @16
    @14
    cmpt
    @12
    cF
    @52
    cr
    cdv
    @12
    vw
    @16
    cr
    cF
    @49
    feqmptd
    oveq2d
    @12
    vw
    @16
    cr
    @1
    wph
    @16
    cr
    @1
    wf
    #
    @11
    wph
    @1
    cdm
    #
    cr
    @1
    wf
    #
    @53
    wph
    @40
    @16
    cr
    wss
    @55
    @41
    cA
    cB
    ioossre
    #
    @16
    cF
    dvfre
    sylancl
    #
    wph
    @54
    @16
    cr
    @1
    dvivth.4
    feq2d
    mpbid
    #
    adantr
    #
    feqmptd
    eqtr3d
    #
    dvmptneg
    #
    dmeqd
    @19
    cvv
    wcel
    #
    @46
    @16
    wceq
    vw
    @16
    vw
    @16
    @19
    cvv
    dmmptg
    @62
    @38
    @14
    negex
    a1i
    mprg
    syl6eq
    wph
    @0
    @9
    simprl
    @12
    @18
    @3
    cneg
    #
    @2
    cneg
    #
    cicc
    co
    #
    cN
    @28
    cfv
    #
    cM
    @28
    cfv
    #
    cicc
    co
    @12
    @9
    @18
    @65
    wcel
    #
    wph
    @0
    @9
    simprr
    #
    @12
    @2
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @8
    cr
    wcel
    @9
    @68
    wb
    wph
    @70
    @11
    wph
    @16
    cr
    cM
    @1
    @58
    dvivth.1
    ffvelrnd
    #
    adantr
    wph
    @71
    @11
    wph
    @54
    cr
    cN
    @1
    @57
    wph
    cN
    @16
    @54
    dvivth.2
    dvivth.4
    eleqtrrd
    #
    ffvelrnd
    #
    adantr
    @12
    @4
    cr
    @8
    wph
    @4
    cr
    wss
    #
    @11
    wph
    @70
    @71
    @75
    @72
    @74
    @2
    @3
    iccssre
    syl2anc
    adantr
    @69
    sseldd
    #
    @2
    @3
    @8
    iccneg
    syl3anc
    mpbid
    @12
    @66
    @63
    @67
    @64
    cicc
    @12
    @66
    cN
    @22
    cfv
    #
    @63
    @12
    cN
    @28
    @22
    @61
    fveq1d
    @12
    @33
    @77
    @63
    wceq
    @34
    vw
    cN
    @19
    @63
    @16
    @22
    @13
    cN
    wceq
    @14
    @3
    @13
    cN
    @1
    fveq2
    negeqd
    @22
    eqid
    #
    @3
    negex
    fvmpt
    syl
    eqtrd
    @12
    @67
    cM
    @22
    cfv
    #
    @64
    @12
    cM
    @28
    @22
    @61
    fveq1d
    @12
    @31
    @79
    @64
    wceq
    @32
    vw
    cM
    @19
    @64
    @16
    @22
    @13
    cM
    wceq
    @14
    @2
    @13
    cM
    @1
    fveq2
    negeqd
    @78
    @2
    negex
    fvmpt
    syl
    eqtrd
    oveq12d
    eleqtrrd
    @30
    eqid
    dvivthlem2
    @12
    @28
    @22
    @61
    rneqd
    eleqtrd
    @18
    cvv
    wcel
    @24
    @21
    wb
    @8
    negex
    vw
    @16
    @19
    @18
    @22
    cvv
    @78
    elrnmpt
    ax-mp
    sylib
    @12
    @20
    @15
    vw
    @16
    @48
    @20
    @8
    @14
    wceq
    @15
    @48
    @8
    @14
    @12
    @8
    cc
    wcel
    @38
    @12
    @8
    @76
    recnd
    adantr
    @12
    vw
    @25
    @14
    cr
    cvv
    @16
    @47
    @50
    @51
    @60
    dvmptcl
    neg11ad
    @8
    @14
    eqcom
    syl6bb
    rexbidva
    mpbid
    @12
    @1
    @16
    wfn
    #
    @10
    @17
    wb
    @12
    @53
    @80
    @59
    @16
    cr
    @1
    ffn
    syl
    vw
    @16
    @8
    @1
    fvelrnb
    syl
    mpbird
    expr
    ssrdv
    wph
    @6
    wa
    @4
    @3
    csn
    #
    @5
    @6
    wph
    @4
    @3
    @3
    cicc
    co
    #
    @81
    @6
    @2
    @3
    @3
    cicc
    cM
    cN
    @1
    fveq2
    oveq1d
    wph
    @3
    cxr
    wcel
    @82
    @81
    wceq
    wph
    @3
    @74
    rexrd
    @3
    iccid
    syl
    sylan9eqr
    wph
    @81
    @5
    wss
    @6
    wph
    @3
    @5
    wph
    @1
    @54
    wfn
    #
    cN
    @54
    wcel
    @3
    @5
    wcel
    wph
    @55
    @83
    @57
    @54
    cr
    @1
    ffn
    syl
    @73
    @54
    cN
    @1
    fnfvelrn
    syl2anc
    snssd
    adantr
    eqsstrd
    wph
    @7
    wa
    vx
    @4
    @5
    wph
    @7
    @9
    @10
    wph
    @7
    @9
    wa
    #
    wa
    vy
    cA
    cB
    @8
    cF
    vy
    @16
    @29
    cF
    cfv
    @8
    @29
    cmul
    co
    cmin
    co
    cmpt
    #
    cN
    cM
    wph
    @33
    @84
    dvivth.2
    adantr
    wph
    @31
    @84
    dvivth.1
    adantr
    wph
    @39
    @84
    dvivth.3
    adantr
    wph
    @54
    @16
    wceq
    @84
    dvivth.4
    adantr
    wph
    @7
    @9
    simprl
    wph
    @7
    @9
    simprr
    @85
    eqid
    dvivthlem2
    expr
    ssrdv
    wph
    cM
    cN
    wph
    @16
    cr
    cM
    @56
    dvivth.1
    sseldi
    wph
    @16
    cr
    cN
    @56
    dvivth.2
    sseldi
    lttri4d
    mpjao3dan
end
