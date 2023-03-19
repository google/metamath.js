include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cabs.mm"
include "cr.mm"
include "ci.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "caddc.mm"
include "ccom.mm"
include "csqrt.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "i1ff.mm"
include "ffvelrnda.mm"
include "absreim.mm"
include "syl2an.mm"
include "anandirs.mm"
include "recnd.mm"
include "sqvald.mm"
include "oveqan12d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "cc.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcl.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "adantlr.mm"
include "ovexd.mm"
include "feqmptd.mm"
include "adantr.mm"
include "fconstmpt.mm"
include "offval2.mm"
include "adantl.mm"
include "wf.mm"
include "absf.mm"
include "fveq2.mm"
include "fmptco.mm"
include "mulcld.mm"
include "adantll.mm"
include "sqrtf.mm"
include "3eqtr4d.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cres.mm"
include "cle.mm"
include "wbr.mm"
include "elrege0.mm"
include "resqrtcl.mm"
include "sylbi.mm"
include "id.mm"
include "ax-mp.mm"
include "reseq1i.mm"
include "wss.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "resmpt.mm"
include "eqtri.mm"
include "fmptd.mm"
include "ge0addcl.mm"
include "oveq12.mm"
include "anidms.mm"
include "feq1d.mm"
include "remulcld.mm"
include "msqge0d.mm"
include "sylanbrc.mm"
include "eqid.mm"
include "mpbird.mm"
include "vtoclga.mm"
include "inidm.mm"
include "off.mm"
include "fco2.mm"
include "syl2anc.mm"
include "crn.mm"
include "cfn.mm"
include "rnco.mm"
include "wfn.mm"
include "ffn.mm"
include "readdcl.mm"
include "remulcl.mm"
include "frn.mm"
include "syl.mm"
include "syl6ss.mm"
include "fnssres.mm"
include "i1fmul.mm"
include "i1fadd.mm"
include "i1frn.mm"
include "fnfi.mm"
include "rnfi.mm"
include "syl5eqel.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "cdif.mm"
include "cnvco.mm"
include "imaeq1i.mm"
include "imaco.mm"
include "i1fima.mm"
include "fveq2i.mm"
include "wn.mm"
include "wo.mm"
include "wne.mm"
include "eldifsni.mm"
include "c0ex.mm"
include "elsn.mm"
include "eqcom.mm"
include "bitri.mm"
include "necon3bbii.mm"
include "sqrt0.mm"
include "eleq1i.mm"
include "xchnxbir.mm"
include "sylibr.mm"
include "olcd.mm"
include "ianor.mm"
include "wb.mm"
include "elpreima.mm"
include "mp2b.mm"
include "i1fima2.mm"
include "i1fd.mm"
include "eqeltrd.mm"

theorem ftc1anclem3
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F e. dom S.1 /\ G e. dom S.1 ) -> ( abs o. ( F oF + ( ( RR X. { _i } ) oF x. G ) ) ) e. dom S.1 )

  proof
    cF
    citg1
    cdm
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    cabs
    cF
    cr
    ci
    csn
    cxp
    #
    cG
    cmul
    cof
    #
    co
    #
    caddc
    cof
    #
    co
    #
    ccom
    #
    csqrt
    cF
    cF
    @5
    co
    #
    cG
    cG
    @5
    co
    #
    @7
    co
    #
    ccom
    #
    @0
    @3
    vx
    cr
    vx
    cv
    #
    cF
    cfv
    #
    ci
    @14
    cG
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cabs
    cfv
    #
    cmpt
    vx
    cr
    @15
    @15
    cmul
    co
    #
    @16
    @16
    cmul
    co
    #
    caddc
    co
    #
    csqrt
    cfv
    #
    cmpt
    @9
    @13
    @3
    vx
    cr
    @19
    @23
    @3
    @14
    cr
    wcel
    #
    wa
    #
    @19
    @15
    c2
    cexp
    co
    #
    @16
    c2
    cexp
    co
    #
    caddc
    co
    #
    csqrt
    cfv
    #
    @23
    @1
    @2
    @24
    @19
    @29
    wceq
    #
    @1
    @24
    wa
    #
    @15
    cr
    wcel
    #
    @16
    cr
    wcel
    @30
    @2
    @24
    wa
    #
    @1
    cr
    cr
    @14
    cF
    cF
    i1ff
    #
    ffvelrnda
    #
    @2
    cr
    cr
    @14
    cG
    cG
    i1ff
    #
    ffvelrnda
    #
    @15
    @16
    absreim
    syl2an
    anandirs
    @25
    @28
    @22
    csqrt
    @1
    @2
    @24
    @28
    @22
    wceq
    @31
    @33
    @26
    @20
    @27
    @21
    caddc
    @31
    @15
    @31
    @15
    @35
    recnd
    #
    sqvald
    @33
    @16
    @33
    @16
    @37
    recnd
    #
    sqvald
    oveqan12d
    anandirs
    fveq2d
    eqtrd
    mpteq2dva
    @3
    vx
    vy
    cr
    cc
    @18
    vy
    cv
    #
    cabs
    cfv
    @19
    @8
    cabs
    @1
    @2
    @24
    @18
    cc
    wcel
    #
    @31
    @15
    cc
    wcel
    @17
    cc
    wcel
    #
    @41
    @33
    @38
    @33
    ci
    cc
    wcel
    #
    @16
    cc
    wcel
    @42
    ax-icn
    @39
    ci
    @16
    mulcl
    sylancr
    @15
    @17
    addcl
    syl2an
    anandirs
    @3
    vx
    cr
    @15
    @17
    caddc
    cF
    @6
    cvv
    cr
    cvv
    cr
    cvv
    wcel
    #
    @3
    reex
    a1i
    #
    @1
    @24
    @32
    @2
    @35
    adantlr
    @25
    ci
    @16
    cmul
    ovexd
    @1
    cF
    vx
    cr
    @15
    cmpt
    wceq
    @2
    @1
    vx
    cr
    cr
    cF
    @34
    feqmptd
    #
    adantr
    @2
    @6
    vx
    cr
    @17
    cmpt
    wceq
    @1
    @2
    vx
    cr
    ci
    @16
    cmul
    @4
    cG
    cvv
    cc
    cr
    @44
    @2
    reex
    a1i
    #
    @43
    @33
    ax-icn
    a1i
    @37
    @4
    vx
    cr
    ci
    cmpt
    wceq
    @2
    vx
    cr
    ci
    fconstmpt
    a1i
    @2
    vx
    cr
    cr
    cG
    @36
    feqmptd
    #
    offval2
    adantl
    offval2
    @3
    vy
    cc
    cr
    cabs
    cc
    cr
    cabs
    wf
    @3
    absf
    a1i
    feqmptd
    @40
    @18
    cabs
    fveq2
    fmptco
    @3
    vx
    vy
    cr
    cc
    @22
    @40
    csqrt
    cfv
    @23
    @12
    csqrt
    @1
    @2
    @24
    @22
    cc
    wcel
    #
    @31
    @20
    cc
    wcel
    #
    @21
    cc
    wcel
    #
    @49
    @33
    @31
    @15
    @15
    @38
    @38
    mulcld
    #
    @33
    @16
    @16
    @39
    @39
    mulcld
    #
    @20
    @21
    addcl
    syl2an
    anandirs
    @3
    vx
    cr
    @20
    @21
    caddc
    @10
    @11
    cvv
    cc
    cc
    @45
    @1
    @24
    @50
    @2
    @52
    adantlr
    @2
    @24
    @51
    @1
    @53
    adantll
    @1
    @10
    vx
    cr
    @20
    cmpt
    wceq
    @2
    @1
    vx
    cr
    @15
    @15
    cmul
    cF
    cF
    cvv
    cr
    cr
    @44
    @1
    reex
    a1i
    #
    @35
    @35
    @46
    @46
    offval2
    adantr
    @2
    @11
    vx
    cr
    @21
    cmpt
    wceq
    @1
    @2
    vx
    cr
    @16
    @16
    cmul
    cG
    cG
    cvv
    cr
    cr
    @47
    @37
    @37
    @48
    @48
    offval2
    adantl
    offval2
    @3
    vy
    cc
    cc
    csqrt
    cc
    cc
    csqrt
    wf
    #
    @3
    sqrtf
    a1i
    feqmptd
    @40
    @22
    csqrt
    fveq2
    fmptco
    3eqtr4d
    @3
    vx
    @13
    @3
    cc0
    cpnf
    cico
    co
    #
    cr
    csqrt
    @56
    cres
    #
    wf
    cr
    @56
    @12
    wf
    cr
    cr
    @13
    wf
    @3
    vx
    @56
    @14
    csqrt
    cfv
    #
    cr
    @57
    @14
    @56
    wcel
    #
    @58
    cr
    wcel
    #
    @3
    @59
    @24
    cc0
    @14
    cle
    wbr
    wa
    @60
    @14
    elrege0
    @14
    resqrtcl
    sylbi
    adantl
    @57
    vx
    cc
    @58
    cmpt
    #
    @56
    cres
    #
    vx
    @56
    @58
    cmpt
    #
    csqrt
    @61
    @56
    @55
    csqrt
    @61
    wceq
    sqrtf
    @55
    vx
    cc
    cc
    csqrt
    @55
    id
    feqmptd
    ax-mp
    reseq1i
    @56
    cc
    wss
    @62
    @63
    wceq
    @56
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    vx
    cc
    @56
    @58
    resmpt
    ax-mp
    eqtri
    fmptd
    @3
    vx
    vy
    cr
    cr
    cr
    caddc
    @56
    @56
    @56
    @10
    @11
    cvv
    cvv
    @59
    @40
    @56
    wcel
    wa
    @14
    @40
    caddc
    co
    #
    @56
    wcel
    @3
    @14
    @40
    ge0addcl
    adantl
    @1
    cr
    @56
    @10
    wf
    #
    @2
    cr
    @56
    vz
    cv
    #
    @66
    @5
    co
    #
    wf
    #
    @65
    vz
    cF
    @0
    @66
    cF
    wceq
    #
    cr
    @56
    @67
    @10
    @69
    @67
    @10
    wceq
    @66
    cF
    @66
    cF
    @5
    oveq12
    anidms
    feq1d
    @66
    @0
    wcel
    #
    @68
    cr
    @56
    vx
    cr
    @14
    @66
    cfv
    #
    @71
    cmul
    co
    #
    cmpt
    #
    wf
    @70
    vx
    cr
    @72
    @56
    @73
    @70
    @24
    wa
    #
    @72
    cr
    wcel
    cc0
    @72
    cle
    wbr
    @72
    @56
    wcel
    @74
    @71
    @71
    @70
    cr
    cr
    @14
    @66
    @66
    i1ff
    #
    ffvelrnda
    #
    @76
    remulcld
    @74
    @71
    @76
    msqge0d
    @72
    elrege0
    sylanbrc
    @73
    eqid
    fmptd
    @70
    cr
    @56
    @67
    @73
    @70
    vx
    cr
    @71
    @71
    cmul
    @66
    @66
    cvv
    cr
    cr
    @44
    @70
    reex
    a1i
    @76
    @76
    @70
    vx
    cr
    cr
    @66
    @75
    feqmptd
    #
    @77
    offval2
    feq1d
    mpbird
    #
    vtoclga
    adantr
    @2
    cr
    @56
    @11
    wf
    #
    @1
    @68
    @79
    vz
    cG
    @0
    @66
    cG
    wceq
    #
    cr
    @56
    @67
    @11
    @80
    @67
    @11
    wceq
    @66
    cG
    @66
    cG
    @5
    oveq12
    anidms
    feq1d
    @78
    vtoclga
    adantl
    @45
    @45
    cr
    inidm
    #
    off
    cr
    @56
    cr
    csqrt
    @12
    fco2
    syl2anc
    @3
    @13
    crn
    #
    csqrt
    @12
    crn
    #
    cres
    #
    crn
    #
    cfn
    csqrt
    @12
    rnco
    @3
    @84
    cfn
    wcel
    #
    @85
    cfn
    wcel
    @3
    @84
    @83
    wfn
    #
    @83
    cfn
    wcel
    #
    @86
    @3
    csqrt
    cc
    wfn
    #
    @83
    cc
    wss
    @87
    @55
    @89
    sqrtf
    cc
    cc
    csqrt
    ffn
    #
    ax-mp
    @3
    @83
    cr
    cc
    @3
    cr
    cr
    @12
    wf
    @83
    cr
    wss
    @3
    vx
    vy
    cr
    cr
    cr
    caddc
    cr
    cr
    cr
    @10
    @11
    cvv
    cvv
    @24
    @40
    cr
    wcel
    wa
    #
    @64
    cr
    wcel
    @3
    @14
    @40
    readdcl
    adantl
    @1
    cr
    cr
    @10
    wf
    @2
    @1
    vx
    vy
    cr
    cr
    cr
    cmul
    cr
    cr
    cr
    cF
    cF
    cvv
    cvv
    @91
    @14
    @40
    cmul
    co
    cr
    wcel
    #
    @1
    @14
    @40
    remulcl
    #
    adantl
    @34
    @34
    @54
    @54
    @81
    off
    adantr
    @2
    cr
    cr
    @11
    wf
    @1
    @2
    vx
    vy
    cr
    cr
    cr
    cmul
    cr
    cr
    cr
    cG
    cG
    cvv
    cvv
    @91
    @92
    @2
    @93
    adantl
    @36
    @36
    @47
    @47
    @81
    off
    adantl
    @45
    @45
    @81
    off
    cr
    cr
    @12
    frn
    syl
    ax-resscn
    syl6ss
    cc
    @83
    csqrt
    fnssres
    sylancr
    @3
    @12
    @0
    wcel
    #
    @88
    @3
    @10
    @11
    @1
    @10
    @0
    wcel
    @2
    @1
    cF
    cF
    @1
    id
    #
    @95
    i1fmul
    adantr
    @2
    @11
    @0
    wcel
    @1
    @2
    cG
    cG
    @2
    id
    #
    @96
    i1fmul
    adantl
    i1fadd
    #
    @12
    i1frn
    syl
    @83
    @84
    fnfi
    syl2anc
    @84
    rnfi
    syl
    syl5eqel
    @3
    @13
    ccnv
    #
    @14
    csn
    #
    cima
    #
    cvol
    cdm
    #
    wcel
    @14
    @82
    cc0
    csn
    cdif
    wcel
    #
    @3
    @100
    @12
    ccnv
    #
    csqrt
    ccnv
    #
    @99
    cima
    #
    cima
    #
    @101
    @100
    @103
    @104
    ccom
    #
    @99
    cima
    @106
    @98
    @107
    @99
    csqrt
    @12
    cnvco
    imaeq1i
    @103
    @104
    @99
    imaco
    eqtri
    #
    @3
    @94
    @106
    @101
    wcel
    @97
    @105
    @12
    i1fima
    syl
    syl5eqel
    adantr
    @3
    @102
    wa
    @100
    cvol
    cfv
    @106
    cvol
    cfv
    #
    cr
    @100
    @106
    cvol
    @108
    fveq2i
    @3
    @94
    cc0
    @105
    wcel
    #
    wn
    #
    @109
    cr
    wcel
    @102
    @97
    @102
    cc0
    cc
    wcel
    #
    wn
    #
    cc0
    csqrt
    cfv
    #
    @99
    wcel
    #
    wn
    #
    wo
    #
    @111
    @102
    @116
    @113
    @102
    @14
    cc0
    wne
    #
    @116
    @14
    @82
    cc0
    eldifsni
    cc0
    @99
    wcel
    #
    @118
    @115
    @119
    @14
    cc0
    @119
    cc0
    @14
    wceq
    @14
    cc0
    wceq
    cc0
    @14
    c0ex
    elsn
    cc0
    @14
    eqcom
    bitri
    necon3bbii
    @114
    cc0
    @99
    sqrt0
    eleq1i
    xchnxbir
    sylibr
    olcd
    @112
    @115
    wa
    #
    @117
    @110
    @112
    @115
    ianor
    @55
    @89
    @110
    @120
    wb
    sqrtf
    @90
    cc
    cc0
    @99
    csqrt
    elpreima
    mp2b
    xchnxbir
    sylibr
    @105
    @12
    i1fima2
    syl2an
    syl5eqel
    i1fd
    eqeltrd
end
