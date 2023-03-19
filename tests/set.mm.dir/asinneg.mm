include "cc.mm"
include "wcel.mm"
include "ci.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "csqrt.mm"
include "cfv.mm"
include "caddc.mm"
include "clog.mm"
include "casin.mm"
include "wceq.mm"
include "ce.mm"
include "cdiv.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "ax-1cn.mm"
include "sqcl.mm"
include "subcl.mm"
include "sylancr.mm"
include "sqrtcld.mm"
include "addcld.mm"
include "asinlem.mm"
include "logcld.mm"
include "efneg.mm"
include "syl.mm"
include "cc0.mm"
include "wne.mm"
include "eflog.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "asinlem2.mm"
include "a1i.mm"
include "negcl.mm"
include "sqcld.mm"
include "divmuld.mm"
include "mpbird.mm"
include "3eqtrd.mm"
include "crn.mm"
include "wb.mm"
include "cim.mm"
include "ccnv.mm"
include "cpi.mm"
include "cioc.mm"
include "cima.mm"
include "negcld.mm"
include "imnegd.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "imcld.mm"
include "renegcld.mm"
include "cre.mm"
include "wn.mm"
include "renegd.mm"
include "asinlem3.mm"
include "recld.mm"
include "le0neg2d.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "0re.mm"
include "lenlt.mm"
include "sylancl.mm"
include "crp.mm"
include "lognegb.mm"
include "rpgt0.mm"
include "rpre.mm"
include "rered.mm"
include "breqtrrd.mm"
include "syl6bir.mm"
include "necon3bd.mm"
include "mpd.mm"
include "necomd.mm"
include "pire.mm"
include "logimcld.mm"
include "simprd.mm"
include "leltned.mm"
include "ltneg.mm"
include "simpld.mm"
include "wi.mm"
include "renegcli.mm"
include "ltle.mm"
include "lenegcon1.mm"
include "cxr.mm"
include "w3a.mm"
include "rexri.mm"
include "elioc2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "eqeltrd.mm"
include "wf.mm"
include "wfn.mm"
include "wa.mm"
include "imf.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "sylanbrc.mm"
include "logrn.mm"
include "syl6eleqr.mm"
include "logeftb.mm"
include "syl3anc.mm"
include "negicn.mm"
include "mulneg2.mm"
include "eqtrd.mm"
include "asinval.mm"
include "negeqd.mm"
include "3eqtr4d.mm"

theorem asinneg
  let cA: class A


  assert |- ( A e. CC -> ( arcsin ` -u A ) = -u ( arcsin ` A ) )

  proof
    cA
    cc
    wcel
    #
    ci
    cneg
    #
    ci
    cA
    cneg
    #
    cmul
    co
    #
    c1
    @2
    c2
    cexp
    co
    #
    cmin
    co
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    @1
    ci
    cA
    cmul
    co
    #
    c1
    cA
    c2
    cexp
    co
    #
    cmin
    co
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    cneg
    #
    @2
    casin
    cfv
    #
    cA
    casin
    cfv
    #
    cneg
    @0
    @9
    @1
    @15
    cneg
    #
    cmul
    co
    #
    @17
    @0
    @8
    @20
    @1
    cmul
    @0
    @8
    @20
    wceq
    #
    @20
    ce
    cfv
    #
    @7
    wceq
    #
    @0
    @23
    c1
    @15
    ce
    cfv
    #
    cdiv
    co
    #
    c1
    @14
    cdiv
    co
    #
    @7
    @0
    @15
    cc
    wcel
    #
    @23
    @26
    wceq
    @0
    @14
    @0
    @10
    @13
    ci
    cc
    wcel
    #
    @0
    @10
    cc
    wcel
    ax-icn
    ci
    cA
    mulcl
    mpan
    @0
    @12
    @0
    c1
    cc
    wcel
    #
    @11
    cc
    wcel
    @12
    cc
    wcel
    ax-1cn
    cA
    sqcl
    c1
    @11
    subcl
    sylancr
    sqrtcld
    addcld
    #
    cA
    asinlem
    #
    logcld
    #
    @15
    efneg
    syl
    @0
    @25
    @14
    c1
    cdiv
    @0
    @14
    cc
    wcel
    #
    @14
    cc0
    wne
    #
    @25
    @14
    wceq
    @31
    @32
    @14
    eflog
    syl2anc
    oveq2d
    @0
    @27
    @7
    wceq
    @14
    @7
    cmul
    co
    c1
    wceq
    cA
    asinlem2
    @0
    c1
    @14
    @7
    @30
    @0
    ax-1cn
    a1i
    @31
    @0
    @3
    @6
    @0
    @29
    @2
    cc
    wcel
    #
    @3
    cc
    wcel
    ax-icn
    cA
    negcl
    #
    ci
    @2
    mulcl
    sylancr
    @0
    @5
    @0
    @30
    @4
    cc
    wcel
    @5
    cc
    wcel
    ax-1cn
    @0
    @2
    @37
    sqcld
    c1
    @4
    subcl
    sylancr
    sqrtcld
    addcld
    #
    @32
    divmuld
    mpbird
    3eqtrd
    @0
    @7
    cc
    wcel
    @7
    cc0
    wne
    #
    @20
    clog
    crn
    #
    wcel
    @22
    @24
    wb
    @38
    @0
    @36
    @39
    @37
    @2
    asinlem
    syl
    @0
    @20
    cim
    ccnv
    cpi
    cneg
    #
    cpi
    cioc
    co
    #
    cima
    #
    @40
    @0
    @20
    cc
    wcel
    #
    @20
    cim
    cfv
    #
    @42
    wcel
    #
    @20
    @43
    wcel
    #
    @0
    @15
    @33
    negcld
    @0
    @45
    @15
    cim
    cfv
    #
    cneg
    #
    @42
    @0
    @15
    @33
    imnegd
    @0
    @49
    cr
    wcel
    #
    @41
    @49
    clt
    wbr
    #
    @49
    cpi
    cle
    wbr
    #
    @49
    @42
    wcel
    #
    @0
    @48
    @0
    @15
    @33
    imcld
    #
    renegcld
    @0
    @48
    cpi
    clt
    wbr
    #
    @51
    @0
    @55
    cpi
    @48
    wne
    @0
    @48
    cpi
    @0
    cc0
    @14
    cneg
    #
    cre
    cfv
    #
    clt
    wbr
    #
    wn
    #
    @48
    cpi
    wne
    @0
    @57
    cc0
    cle
    wbr
    #
    @59
    @0
    @57
    @14
    cre
    cfv
    #
    cneg
    #
    cc0
    cle
    @0
    @14
    @31
    renegd
    @0
    cc0
    @61
    cle
    wbr
    @62
    cc0
    cle
    wbr
    cA
    asinlem3
    @0
    @61
    @0
    @14
    @31
    recld
    le0neg2d
    mpbid
    eqbrtrd
    @0
    @57
    cr
    wcel
    cc0
    cr
    wcel
    @60
    @59
    wb
    @0
    @56
    @0
    @14
    @31
    negcld
    recld
    0re
    @57
    cc0
    lenlt
    sylancl
    mpbid
    @0
    @58
    @48
    cpi
    @0
    @48
    cpi
    wceq
    #
    @56
    crp
    wcel
    #
    @58
    @0
    @34
    @35
    @64
    @63
    wb
    @31
    @32
    @14
    lognegb
    syl2anc
    @64
    cc0
    @56
    @57
    clt
    @56
    rpgt0
    @64
    @56
    @56
    rpre
    rered
    breqtrrd
    syl6bir
    necon3bd
    mpd
    necomd
    @0
    @48
    cpi
    @54
    cpi
    cr
    wcel
    #
    @0
    pire
    a1i
    @0
    @41
    @48
    clt
    wbr
    #
    @48
    cpi
    cle
    wbr
    #
    @0
    @14
    @31
    @32
    logimcld
    #
    simprd
    leltned
    mpbird
    @0
    @48
    cr
    wcel
    #
    @65
    @55
    @51
    wb
    @54
    pire
    @48
    cpi
    ltneg
    sylancl
    mpbid
    @0
    @41
    @48
    cle
    wbr
    #
    @52
    @0
    @66
    @70
    @0
    @66
    @67
    @68
    simpld
    @0
    @41
    cr
    wcel
    @69
    @66
    @70
    wi
    cpi
    pire
    renegcli
    #
    @54
    @41
    @48
    ltle
    sylancr
    mpd
    @0
    @65
    @69
    @70
    @52
    wb
    pire
    @54
    cpi
    @48
    lenegcon1
    sylancr
    mpbid
    @41
    cxr
    wcel
    @65
    @53
    @50
    @51
    @52
    w3a
    wb
    @41
    @71
    rexri
    pire
    @41
    cpi
    @49
    elioc2
    mp2an
    syl3anbrc
    eqeltrd
    cc
    cr
    cim
    wf
    cim
    cc
    wfn
    @47
    @44
    @46
    wa
    wb
    imf
    cc
    cr
    cim
    ffn
    cc
    @20
    @42
    cim
    elpreima
    mp2b
    sylanbrc
    logrn
    syl6eleqr
    @7
    @20
    logeftb
    syl3anc
    mpbird
    oveq2d
    @0
    @1
    cc
    wcel
    @28
    @21
    @17
    wceq
    negicn
    @33
    @1
    @15
    mulneg2
    sylancr
    eqtrd
    @0
    @36
    @18
    @9
    wceq
    @37
    @2
    asinval
    syl
    @0
    @19
    @16
    cA
    asinval
    negeqd
    3eqtr4d
end
