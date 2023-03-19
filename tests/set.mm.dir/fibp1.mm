include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfib.mm"
include "cfv.mm"
include "cc0.mm"
include "cs2.mm"
include "cn0.mm"
include "cword.mm"
include "chash.mm"
include "ccnv.mm"
include "c2.mm"
include "cuz.mm"
include "cima.mm"
include "cin.mm"
include "cv.mm"
include "cmin.mm"
include "cmpt.mm"
include "csseq.mm"
include "cfzo.mm"
include "cres.mm"
include "wceq.mm"
include "df-fib.mm"
include "fveq1i.mm"
include "a1i.mm"
include "cvv.mm"
include "nn0ex.mm"
include "0nn0.mm"
include "1nn0.mm"
include "s2cld.mm"
include "eqid.mm"
include "wf.mm"
include "fiblem.mm"
include "eluzp1p1.mm"
include "nnuz.mm"
include "eleq2s.mm"
include "s2len.mm"
include "1p1e2.mm"
include "eqtr4i.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "sseqp1.mm"
include "id.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "fveq12d.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "wa.mm"
include "simpr.mm"
include "reseq1d.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "sseqf.mm"
include "feq1d.mm"
include "mpbird.mm"
include "nnnn0.mm"
include "nn0addcld.mm"
include "subiwrdlen.mm"
include "adantr.mm"
include "eqtrd.mm"
include "nncn.mm"
include "1cnd.mm"
include "2cnd.mm"
include "addsubassd.mm"
include "subsub2d.mm"
include "2m1e1.mm"
include "oveq2i.mm"
include "3eqtr2d.mm"
include "fveq1d.mm"
include "clt.mm"
include "wbr.mm"
include "nnm1nn0.mm"
include "peano2nn.mm"
include "nnre.mm"
include "cr.mm"
include "2re.mm"
include "readdcld.mm"
include "1red.mm"
include "crp.mm"
include "2rp.mm"
include "ltaddrpd.mm"
include "ltsub1dd.mm"
include "syl6eq.mm"
include "breqtrd.mm"
include "elfzo0.mm"
include "syl3anbrc.mm"
include "fvres.mm"
include "syl.mm"
include "3eqtrd.mm"
include "simpl.mm"
include "nncnd.mm"
include "pncand.mm"
include "cfz.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "cz.mm"
include "nnz.mm"
include "fzval3.mm"
include "eleqtrd.mm"
include "syldan.mm"
include "subiwrd.mm"
include "ovex.mm"
include "eqeltri.mm"
include "resex.mm"
include "syl6eleq.mm"
include "eqeltrd.mm"
include "cpnf.mm"
include "csn.mm"
include "cun.mm"
include "wfn.mm"
include "wb.mm"
include "hashf.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "sylanbrc.mm"
include "elind.mm"
include "eqeltrrd.mm"
include "fvmptd.mm"

theorem fibp1
  let cN: class N
  let vt: setvar t
  let vw: setvar w


  assert |- ( N e. NN -> ( Fibci ` ( N + 1 ) ) = ( ( Fibci ` ( N - 1 ) ) + ( Fibci ` N ) ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c1
    caddc
    co
    #
    cfib
    cfv
    #
    @1
    cc0
    c1
    cs2
    #
    vw
    cn0
    cword
    #
    chash
    ccnv
    #
    c2
    cuz
    cfv
    #
    cima
    #
    cin
    #
    vw
    cv
    #
    chash
    cfv
    #
    c2
    cmin
    co
    #
    @9
    cfv
    #
    @10
    c1
    cmin
    co
    #
    @9
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    csseq
    co
    #
    cfv
    #
    @17
    cc0
    @1
    cfzo
    co
    #
    cres
    #
    @16
    cfv
    cN
    c1
    cmin
    co
    #
    cfib
    cfv
    #
    cN
    cfib
    cfv
    #
    caddc
    co
    #
    @2
    @18
    wceq
    @0
    @1
    cfib
    @17
    vw
    df-fib
    #
    fveq1i
    a1i
    @0
    cn0
    @16
    @3
    @1
    @4
    @5
    @3
    chash
    cfv
    #
    cuz
    cfv
    #
    cima
    cin
    #
    cn0
    cvv
    wcel
    @0
    nn0ex
    a1i
    #
    @0
    cc0
    c1
    cn0
    cc0
    cn0
    wcel
    @0
    0nn0
    a1i
    c1
    cn0
    wcel
    @0
    1nn0
    a1i
    #
    s2cld
    #
    @28
    eqid
    #
    @28
    cn0
    @16
    wf
    @0
    vw
    fiblem
    a1i
    #
    @0
    @1
    c1
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @27
    @1
    @35
    wcel
    cN
    c1
    cuz
    cfv
    cn
    c1
    cN
    eluzp1p1
    nnuz
    eleq2s
    #
    @26
    @34
    cuz
    @26
    c2
    @34
    cc0
    c1
    s2len
    1p1e2
    eqtr4i
    fveq2i
    syl6eleqr
    sseqp1
    @0
    vt
    @20
    vt
    cv
    #
    chash
    cfv
    #
    c2
    cmin
    co
    #
    @37
    cfv
    #
    @38
    c1
    cmin
    co
    #
    @37
    cfv
    #
    caddc
    co
    #
    @24
    @8
    @16
    cvv
    @16
    vt
    @8
    @43
    cmpt
    wceq
    @0
    vw
    vt
    @8
    @15
    @43
    @9
    @37
    wceq
    #
    @12
    @40
    @14
    @42
    caddc
    @44
    @11
    @39
    @9
    @37
    @44
    id
    #
    @44
    @10
    @38
    c2
    cmin
    @9
    @37
    chash
    fveq2
    #
    oveq1d
    fveq12d
    @44
    @13
    @41
    @9
    @37
    @45
    @44
    @10
    @38
    c1
    cmin
    @46
    oveq1d
    fveq12d
    oveq12d
    cbvmptv
    a1i
    @0
    @37
    @20
    wceq
    #
    @37
    cfib
    @19
    cres
    #
    wceq
    #
    @43
    @24
    wceq
    @0
    @47
    wa
    #
    @37
    @20
    @48
    @0
    @47
    simpr
    @50
    cfib
    @17
    @19
    cfib
    @17
    wceq
    #
    @50
    @25
    a1i
    reseq1d
    eqtr4d
    @0
    @49
    wa
    #
    @40
    @22
    @42
    @23
    caddc
    @52
    @40
    @21
    @37
    cfv
    @21
    @48
    cfv
    #
    @22
    @52
    @39
    @21
    @37
    @52
    @39
    @1
    c2
    cmin
    co
    #
    @21
    @52
    @38
    @1
    c2
    cmin
    @52
    @38
    @48
    chash
    cfv
    #
    @1
    @52
    @37
    @48
    chash
    @0
    @49
    simpr
    #
    fveq2d
    @0
    @55
    @1
    wceq
    @49
    @0
    cn0
    cfib
    @1
    @29
    @0
    cn0
    cn0
    cfib
    wf
    cn0
    cn0
    @17
    wf
    @0
    cn0
    @16
    @3
    @28
    @29
    @31
    @32
    @33
    sseqf
    @0
    cn0
    cn0
    cfib
    @17
    @51
    @0
    @25
    a1i
    #
    feq1d
    mpbird
    #
    @0
    cN
    c1
    cN
    nnnn0
    #
    @30
    nn0addcld
    #
    subiwrdlen
    #
    adantr
    eqtrd
    #
    oveq1d
    @0
    @54
    @21
    wceq
    @49
    @0
    @54
    cN
    c1
    c2
    cmin
    co
    caddc
    co
    cN
    c2
    c1
    cmin
    co
    #
    cmin
    co
    #
    @21
    @0
    cN
    c1
    c2
    cN
    nncn
    #
    @0
    1cnd
    #
    @0
    2cnd
    #
    addsubassd
    @0
    cN
    c2
    c1
    @65
    @67
    @66
    subsub2d
    @64
    @21
    wceq
    @0
    @63
    c1
    cN
    cmin
    2m1e1
    oveq2i
    a1i
    3eqtr2d
    adantr
    eqtrd
    fveq2d
    @52
    @21
    @37
    @48
    @56
    fveq1d
    @52
    @21
    @19
    wcel
    #
    @53
    @22
    wceq
    @0
    @68
    @49
    @0
    @21
    cn0
    wcel
    @1
    cn
    wcel
    @21
    @1
    clt
    wbr
    @68
    cN
    nnm1nn0
    cN
    peano2nn
    @0
    @21
    cN
    c2
    caddc
    co
    #
    c1
    cmin
    co
    #
    @1
    clt
    @0
    cN
    @69
    c1
    cN
    nnre
    #
    @0
    cN
    c2
    @71
    c2
    cr
    wcel
    @0
    2re
    a1i
    readdcld
    @0
    1red
    @0
    cN
    c2
    @71
    c2
    crp
    wcel
    @0
    2rp
    a1i
    ltaddrpd
    ltsub1dd
    @0
    @70
    cN
    @63
    caddc
    co
    @1
    @0
    cN
    c2
    c1
    @65
    @67
    @66
    addsubassd
    @63
    c1
    cN
    caddc
    2m1e1
    oveq2i
    syl6eq
    breqtrd
    @21
    @1
    elfzo0
    syl3anbrc
    adantr
    @21
    @19
    cfib
    fvres
    syl
    3eqtrd
    @52
    @42
    cN
    @37
    cfv
    cN
    @48
    cfv
    #
    @23
    @52
    @41
    cN
    @37
    @52
    @41
    @1
    c1
    cmin
    co
    cN
    @52
    @38
    @1
    c1
    cmin
    @62
    oveq1d
    @52
    cN
    c1
    @52
    cN
    @0
    @49
    simpl
    nncnd
    @52
    1cnd
    pncand
    eqtrd
    fveq2d
    @52
    cN
    @37
    @48
    @56
    fveq1d
    @52
    cN
    @19
    wcel
    #
    @72
    @23
    wceq
    @0
    @73
    @49
    @0
    cN
    cc0
    cN
    cfz
    co
    #
    @19
    @0
    cN
    cn0
    wcel
    cN
    @74
    wcel
    @59
    cN
    nn0fz0
    sylib
    @0
    cN
    cz
    wcel
    @74
    @19
    wceq
    cN
    nnz
    cc0
    cN
    fzval3
    syl
    eleqtrd
    adantr
    cN
    @19
    cfib
    fvres
    syl
    3eqtrd
    oveq12d
    syldan
    @0
    @48
    @20
    @8
    @0
    cfib
    @17
    @19
    @57
    reseq1d
    @0
    @4
    @7
    @48
    @0
    cn0
    cfib
    @1
    @29
    @58
    @60
    subiwrd
    @0
    @48
    cvv
    wcel
    #
    @55
    @6
    wcel
    #
    @48
    @7
    wcel
    #
    @75
    @0
    cfib
    @19
    cfib
    @17
    cvv
    @25
    @3
    @16
    csseq
    ovex
    eqeltri
    resex
    a1i
    @0
    @55
    @1
    @6
    @61
    @0
    @1
    @35
    @6
    @36
    @34
    c2
    cuz
    1p1e2
    fveq2i
    syl6eleq
    eqeltrd
    cvv
    cn0
    cpnf
    csn
    cun
    #
    chash
    wf
    chash
    cvv
    wfn
    @77
    @75
    @76
    wa
    wb
    hashf
    cvv
    @78
    chash
    ffn
    cvv
    @48
    @6
    chash
    elpreima
    mp2b
    sylanbrc
    elind
    eqeltrrd
    @24
    cvv
    wcel
    @0
    @22
    @23
    caddc
    ovex
    a1i
    fvmptd
    3eqtrd
end
