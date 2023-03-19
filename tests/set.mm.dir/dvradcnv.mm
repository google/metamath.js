include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cabs.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cif.mm"
include "cn0.mm"
include "cv.mm"
include "cmul.mm"
include "cmpt.mm"
include "cneg.mm"
include "cshi.mm"
include "nn0uz.mm"
include "wcel.mm"
include "1nn0.mm"
include "a1i.mm"
include "wa.mm"
include "caddc.mm"
include "cexp.mm"
include "cr.mm"
include "cc.mm"
include "ax-1cn.mm"
include "nn0cn.mm"
include "adantl.mm"
include "nn0ex.mm"
include "mptex.mm"
include "shftval4.mm"
include "sylancr.mm"
include "addcom.mm"
include "fveq2d.mm"
include "peano2nn0.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "pserval2.mm"
include "syl2an.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "nn0red.mm"
include "wf.mm"
include "ffvelrn.mm"
include "expcl.mm"
include "mulcld.mm"
include "abscld.mm"
include "remulcld.mm"
include "eqeltrd.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq2.mm"
include "nn0cnd.mm"
include "sylan.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wbr.mm"
include "ccom.mm"
include "cbvmptv.mm"
include "radcnvlt1.mm"
include "simpld.mm"
include "climdm.mm"
include "sylib.mm"
include "cz.mm"
include "wb.mm"
include "0z.mm"
include "neg1z.mm"
include "isershft.mm"
include "mp2an.mm"
include "seqex.mm"
include "fvex.mm"
include "breldm.mm"
include "cuz.mm"
include "cle.mm"
include "neg1cn.mm"
include "addid2i.mm"
include "0le1.mm"
include "1re.mm"
include "le0neg2.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "eqbrtri.mm"
include "eqeltri.mm"
include "eluz1i.mm"
include "mpbir2an.mm"
include "eluzelcn.mm"
include "nn0re.mm"
include "psergf.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "fmptd.mm"
include "eluzp1p1.mm"
include "oveq1i.mm"
include "1pneg1e0.mm"
include "addcomli.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "syl6eleqr.mm"
include "iserex.mm"
include "mpbid.mm"
include "1red.mm"
include "wn.mm"
include "wne.mm"
include "crp.mm"
include "df-ne.mm"
include "biimpri.mm"
include "absrpcl.mm"
include "rprecred.mm"
include "ifclda.mm"
include "breq2d.mm"
include "cn.mm"
include "elnnuz.mm"
include "nnnn0.mm"
include "sylbir.mm"
include "nn0ge0d.mm"
include "absge0d.mm"
include "mulge0d.mm"
include "sylan2.mm"
include "adantr.mm"
include "simpr.mm"
include "sylibr.mm"
include "0expd.mm"
include "sylan9eqr.mm"
include "mul01d.mm"
include "abs00bd.mm"
include "mulid2d.mm"
include "3brtr4d.mm"
include "mulassd.mm"
include "absmuld.mm"
include "absidd.mm"
include "oveq1d.mm"
include "eqle.mm"
include "syl2anc.mm"
include "rpreccld.mm"
include "rpcnd.mm"
include "mul12d.mm"
include "ad2antrr.mm"
include "absdivd.mm"
include "divassd.mm"
include "cmin.mm"
include "pncan.mm"
include "sylancl.mm"
include "nn0zd.mm"
include "expm1d.mm"
include "eqtr3d.mm"
include "eqtr4d.mm"
include "rpne0d.mm"
include "divrec2d.mm"
include "3eqtr3rd.mm"
include "breqtrrd.mm"
include "sylanl2.mm"
include "sylan2br.mm"
include "ifbothda.mm"
include "cvgcmpce.mm"

theorem dvradcnv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vn: setvar n
  let cG: class G
  let cH: class H
  let cX: class X
  let vr: setvar r
  let vk: setvar k
  let vi: setvar i
  assume dvradcnv.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume dvradcnv.r: |- R = sup ( { r e. RR | seq 0 ( + , ( G ` r ) ) e. dom ~~> } , RR* , < )
  assume dvradcnv.h: |- H = ( n e. NN0 |-> ( ( ( n + 1 ) x. ( A ` ( n + 1 ) ) ) x. ( X ^ n ) ) )
  assume dvradcnv.a: |- ( ph -> A : NN0 --> CC )
  assume dvradcnv.x: |- ( ph -> X e. CC )
  assume dvradcnv.l: |- ( ph -> ( abs ` X ) < R )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint G r
  disjoint n r
  disjoint X n
  disjoint r x
  disjoint X r
  disjoint X x
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint i k
  disjoint i r
  disjoint G i
  disjoint k r
  disjoint G k
  disjoint H k
  disjoint i n
  disjoint i x
  disjoint X i
  disjoint X k
  disjoint i ph
  disjoint k ph
  assert |- ( ph -> seq 0 ( + , H ) e. dom ~~> )

  proof
    wph
    cX
    cc0
    wceq
    #
    c1
    c1
    cX
    cabs
    cfv
    #
    cdiv
    co
    #
    cif
    #
    vk
    vi
    cn0
    vi
    cv
    #
    @4
    cX
    cG
    cfv
    #
    cfv
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    c1
    cneg
    #
    cshi
    co
    #
    cH
    cc0
    c1
    cn0
    nn0uz
    c1
    cn0
    wcel
    wph
    1nn0
    a1i
    wph
    vk
    cv
    #
    cn0
    wcel
    #
    wa
    #
    @12
    @11
    cfv
    #
    @12
    c1
    caddc
    co
    #
    @16
    cA
    cfv
    #
    cX
    @16
    cexp
    co
    #
    cmul
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cr
    @14
    @15
    c1
    @12
    caddc
    co
    #
    @9
    cfv
    #
    @16
    @9
    cfv
    #
    @21
    @14
    c1
    cc
    wcel
    #
    @12
    cc
    wcel
    #
    @15
    @23
    wceq
    #
    ax-1cn
    @13
    @26
    wph
    @12
    nn0cn
    adantl
    #
    c1
    @12
    @9
    vi
    cn0
    @8
    nn0ex
    mptex
    #
    shftval4
    #
    sylancr
    @14
    @22
    @16
    @9
    @14
    @25
    @26
    @22
    @16
    wceq
    #
    ax-1cn
    @28
    c1
    @12
    addcom
    #
    sylancr
    fveq2d
    @14
    @24
    @16
    @16
    @5
    cfv
    #
    cabs
    cfv
    #
    cmul
    co
    #
    @21
    @14
    @16
    cn0
    wcel
    #
    @24
    @35
    wceq
    @13
    @36
    wph
    @12
    peano2nn0
    #
    adantl
    #
    vi
    @16
    @8
    @35
    cn0
    @9
    @4
    @16
    wceq
    #
    @4
    @16
    @7
    @34
    cmul
    @39
    id
    @39
    @6
    @33
    cabs
    @4
    @16
    @5
    fveq2
    fveq2d
    oveq12d
    @9
    eqid
    #
    @16
    @34
    cmul
    ovex
    fvmpt
    syl
    @14
    @34
    @20
    @16
    cmul
    @14
    @33
    @19
    cabs
    wph
    cX
    cc
    wcel
    #
    @36
    @33
    @19
    wceq
    @13
    dvradcnv.x
    @37
    vx
    cA
    vn
    cG
    @16
    cX
    dvradcnv.g
    pserval2
    syl2an
    fveq2d
    oveq2d
    eqtrd
    3eqtrd
    #
    @14
    @16
    @20
    @14
    @16
    @38
    nn0red
    #
    @14
    @19
    @14
    @17
    @18
    wph
    cn0
    cc
    cA
    wf
    @36
    @17
    cc
    wcel
    #
    @13
    dvradcnv.a
    @37
    cn0
    cc
    @16
    cA
    ffvelrn
    syl2an
    #
    wph
    @41
    @36
    @18
    cc
    wcel
    #
    @13
    dvradcnv.x
    @37
    cX
    @16
    expcl
    syl2an
    #
    mulcld
    #
    abscld
    #
    remulcld
    #
    eqeltrd
    @14
    @12
    cH
    cfv
    #
    @16
    @17
    cmul
    co
    #
    cX
    @12
    cexp
    co
    #
    cmul
    co
    #
    cc
    @13
    @51
    @54
    wceq
    wph
    vn
    @12
    vn
    cv
    #
    c1
    caddc
    co
    #
    @56
    cA
    cfv
    #
    cmul
    co
    #
    cX
    @55
    cexp
    co
    #
    cmul
    co
    @54
    cn0
    cH
    vn
    vk
    weq
    #
    @58
    @52
    @59
    @53
    cmul
    @60
    @56
    @16
    @57
    @17
    cmul
    @55
    @12
    c1
    caddc
    oveq1
    #
    @60
    @56
    @16
    cA
    @61
    fveq2d
    oveq12d
    @55
    @12
    cX
    cexp
    oveq2
    oveq12d
    dvradcnv.h
    @52
    @53
    cmul
    ovex
    fvmpt
    adantl
    #
    @14
    @52
    @53
    @14
    @16
    @17
    @14
    @16
    @38
    nn0cnd
    #
    @45
    mulcld
    #
    wph
    @41
    @13
    @53
    cc
    wcel
    dvradcnv.x
    cX
    @12
    expcl
    sylan
    #
    mulcld
    #
    eqeltrd
    wph
    caddc
    @11
    cc0
    @10
    caddc
    co
    #
    cseq
    #
    cli
    cdm
    #
    wcel
    #
    caddc
    @11
    cc0
    cseq
    @69
    wcel
    wph
    @68
    caddc
    @9
    cc0
    cseq
    #
    cli
    cfv
    #
    cli
    wbr
    #
    @70
    wph
    @71
    @72
    cli
    wbr
    #
    @73
    wph
    @71
    @69
    wcel
    #
    @74
    wph
    @75
    caddc
    cabs
    @5
    ccom
    cc0
    cseq
    @69
    wcel
    wph
    vx
    cA
    cR
    vk
    vn
    cG
    @9
    cX
    vr
    dvradcnv.g
    dvradcnv.a
    dvradcnv.r
    dvradcnv.x
    dvradcnv.l
    vi
    vk
    cn0
    @8
    @12
    @12
    @5
    cfv
    #
    cabs
    cfv
    #
    cmul
    co
    vi
    vk
    weq
    #
    @4
    @12
    @7
    @77
    cmul
    @78
    id
    @78
    @6
    @76
    cabs
    @4
    @12
    @5
    fveq2
    fveq2d
    oveq12d
    cbvmptv
    radcnvlt1
    simpld
    @71
    climdm
    sylib
    cc0
    cz
    wcel
    #
    @10
    cz
    wcel
    @74
    @73
    wb
    0z
    neg1z
    @72
    caddc
    @9
    cc0
    @10
    @29
    isershft
    mp2an
    sylib
    @68
    @72
    cli
    caddc
    @11
    @67
    seqex
    @71
    cli
    fvex
    breldm
    syl
    wph
    vk
    @11
    @67
    cc0
    @67
    cuz
    cfv
    #
    @80
    eqid
    cc0
    @80
    wcel
    #
    wph
    @81
    @79
    @67
    cc0
    cle
    wbr
    0z
    @67
    @10
    cc0
    cle
    @10
    neg1cn
    addid2i
    #
    cc0
    c1
    cle
    wbr
    #
    @10
    cc0
    cle
    wbr
    #
    0le1
    c1
    cr
    wcel
    @83
    @84
    wb
    1re
    c1
    le0neg2
    ax-mp
    mpbi
    eqbrtri
    @67
    cc0
    @67
    @10
    cz
    @82
    neg1z
    eqeltri
    eluz1i
    mpbir2an
    a1i
    wph
    @12
    @80
    wcel
    #
    wa
    #
    @15
    @23
    cc
    @86
    @25
    @26
    @27
    ax-1cn
    @85
    @26
    wph
    @67
    @12
    eluzelcn
    #
    adantl
    @30
    sylancr
    wph
    cn0
    cc
    @9
    wf
    @22
    cn0
    wcel
    @23
    cc
    wcel
    @85
    wph
    vi
    cn0
    @8
    cc
    @9
    wph
    @4
    cn0
    wcel
    #
    wa
    #
    @8
    @89
    @4
    @7
    @88
    @4
    cr
    wcel
    wph
    @4
    nn0re
    adantl
    @89
    @6
    wph
    cn0
    cc
    @4
    @5
    wph
    vx
    cA
    vn
    cG
    cX
    dvradcnv.g
    dvradcnv.a
    dvradcnv.x
    psergf
    ffvelrnda
    abscld
    remulcld
    recnd
    @40
    fmptd
    @85
    @22
    @16
    cn0
    @85
    @25
    @26
    @31
    ax-1cn
    @87
    @32
    sylancr
    @85
    @16
    @67
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    cn0
    @67
    @12
    eluzp1p1
    cn0
    cc0
    cuz
    cfv
    @91
    nn0uz
    @90
    cc0
    cuz
    @90
    @10
    c1
    caddc
    co
    cc0
    @67
    @10
    c1
    caddc
    @82
    oveq1i
    c1
    @10
    cc0
    ax-1cn
    neg1cn
    1pneg1e0
    addcomli
    eqtri
    fveq2i
    eqtr4i
    syl6eleqr
    eqeltrd
    cn0
    cc
    @22
    @9
    ffvelrn
    syl2an
    eqeltrd
    iserex
    mpbid
    wph
    @0
    c1
    @2
    cr
    wph
    @0
    wa
    1red
    wph
    @0
    wn
    #
    wa
    @1
    wph
    @41
    cX
    cc0
    wne
    #
    @1
    crp
    wcel
    #
    @92
    dvradcnv.x
    @93
    @92
    cX
    cc0
    df-ne
    #
    biimpri
    cX
    absrpcl
    #
    syl2an
    rprecred
    ifclda
    wph
    @12
    c1
    cuz
    cfv
    wcel
    #
    wa
    #
    @54
    cabs
    cfv
    #
    @3
    @21
    cmul
    co
    #
    @51
    cabs
    cfv
    #
    @3
    @15
    cmul
    co
    #
    cle
    @0
    @99
    c1
    @21
    cmul
    co
    #
    cle
    wbr
    @99
    @2
    @21
    cmul
    co
    #
    cle
    wbr
    #
    @99
    @100
    cle
    wbr
    @98
    c1
    @2
    c1
    @3
    wceq
    @103
    @100
    @99
    cle
    c1
    @3
    @21
    cmul
    oveq1
    breq2d
    @2
    @3
    wceq
    @104
    @100
    @99
    cle
    @2
    @3
    @21
    cmul
    oveq1
    breq2d
    @98
    @0
    wa
    #
    cc0
    @21
    @99
    @103
    cle
    @98
    cc0
    @21
    cle
    wbr
    #
    @0
    @97
    wph
    @13
    @107
    @97
    @12
    cn
    wcel
    #
    @13
    @12
    elnnuz
    #
    @12
    nnnn0
    sylbir
    #
    @14
    @16
    @20
    @43
    @49
    @14
    @16
    @38
    nn0ge0d
    #
    @14
    @19
    @48
    absge0d
    mulge0d
    sylan2
    adantr
    @106
    @54
    @106
    @54
    @52
    cc0
    cmul
    co
    #
    cc0
    @106
    @53
    cc0
    @52
    cmul
    @0
    @98
    @53
    cc0
    @12
    cexp
    co
    cc0
    cX
    cc0
    @12
    cexp
    oveq1
    @98
    @12
    @98
    @97
    @108
    wph
    @97
    simpr
    @109
    sylibr
    0expd
    sylan9eqr
    oveq2d
    @98
    @112
    cc0
    wceq
    #
    @0
    @97
    wph
    @13
    @113
    @110
    @14
    @52
    @64
    mul01d
    sylan2
    adantr
    eqtrd
    abs00bd
    @98
    @103
    @21
    wceq
    #
    @0
    @97
    wph
    @13
    @114
    @110
    @14
    @21
    @14
    @21
    @50
    recnd
    mulid2d
    sylan2
    adantr
    3brtr4d
    @92
    @98
    @93
    @105
    @95
    @97
    wph
    @13
    @93
    @105
    @110
    @14
    @93
    wa
    #
    @99
    @16
    @17
    @53
    cmul
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    @104
    cle
    @14
    @99
    @118
    cle
    wbr
    #
    @93
    @14
    @99
    cr
    wcel
    @99
    @118
    wceq
    @119
    @14
    @54
    @66
    abscld
    @14
    @99
    @16
    @116
    cmul
    co
    #
    cabs
    cfv
    @16
    cabs
    cfv
    #
    @117
    cmul
    co
    @118
    @14
    @54
    @120
    cabs
    @14
    @16
    @17
    @53
    @63
    @45
    @65
    mulassd
    fveq2d
    @14
    @16
    @116
    @63
    @14
    @17
    @53
    @45
    @65
    mulcld
    absmuld
    @14
    @121
    @16
    @117
    cmul
    @14
    @16
    @43
    @111
    absidd
    oveq1d
    3eqtrd
    @99
    @118
    eqle
    syl2anc
    adantr
    @115
    @104
    @16
    @2
    @20
    cmul
    co
    #
    cmul
    co
    @118
    @115
    @2
    @16
    @20
    @115
    @2
    @14
    @41
    @93
    @2
    crp
    wcel
    wph
    @41
    @13
    dvradcnv.x
    adantr
    #
    @41
    @93
    wa
    @1
    @96
    rpreccld
    sylan
    rpcnd
    @14
    @16
    cc
    wcel
    @93
    @63
    adantr
    @115
    @20
    @14
    @20
    cr
    wcel
    @93
    @49
    adantr
    recnd
    #
    mul12d
    @115
    @122
    @117
    @16
    cmul
    @115
    @19
    cX
    cdiv
    co
    #
    cabs
    cfv
    @20
    @1
    cdiv
    co
    @117
    @122
    @115
    @19
    cX
    @14
    @19
    cc
    wcel
    @93
    @48
    adantr
    wph
    @41
    @13
    @93
    dvradcnv.x
    ad2antrr
    #
    @14
    @93
    simpr
    #
    absdivd
    @115
    @125
    @116
    cabs
    @115
    @125
    @17
    @18
    cX
    cdiv
    co
    #
    cmul
    co
    @116
    @115
    @17
    @18
    cX
    @14
    @44
    @93
    @45
    adantr
    @14
    @46
    @93
    @47
    adantr
    @126
    @127
    divassd
    @115
    @53
    @128
    @17
    cmul
    @115
    cX
    @16
    c1
    cmin
    co
    #
    cexp
    co
    @53
    @128
    @115
    @129
    @12
    cX
    cexp
    @115
    @26
    @25
    @129
    @12
    wceq
    @14
    @26
    @93
    @28
    adantr
    ax-1cn
    @12
    c1
    pncan
    sylancl
    oveq2d
    @115
    cX
    @16
    @126
    @127
    @14
    @16
    cz
    wcel
    @93
    @14
    @16
    @38
    nn0zd
    adantr
    expm1d
    eqtr3d
    oveq2d
    eqtr4d
    fveq2d
    @115
    @20
    @1
    @124
    @115
    @1
    wph
    @1
    cr
    wcel
    @13
    @93
    wph
    cX
    dvradcnv.x
    abscld
    ad2antrr
    recnd
    @115
    @1
    @14
    @41
    @93
    @94
    @123
    @96
    sylan
    rpne0d
    divrec2d
    3eqtr3rd
    oveq2d
    eqtrd
    breqtrrd
    sylanl2
    sylan2br
    ifbothda
    @97
    wph
    @13
    @101
    @99
    wceq
    @110
    @14
    @51
    @54
    cabs
    @62
    fveq2d
    sylan2
    @97
    wph
    @13
    @102
    @100
    wceq
    @110
    @14
    @15
    @21
    @3
    cmul
    @42
    oveq2d
    sylan2
    3brtr4d
    cvgcmpce
end
