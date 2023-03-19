include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "wcel.mm"
include "cicc.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cima.mm"
include "cuni.mm"
include "cvol.mm"
include "cdm.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "weq.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "elrab.mm"
include "simprr.mm"
include "fvex.mm"
include "elpw.mm"
include "sylibr.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "wfun.mm"
include "wb.mm"
include "cxr.mm"
include "cxp.mm"
include "wf.mm"
include "iccf.mm"
include "ffun.mm"
include "ax-mp.mm"
include "ssrab2.mm"
include "cle.mm"
include "cr.mm"
include "cin.mm"
include "cz.mm"
include "cn0.mm"
include "dyadf.mm"
include "frn.mm"
include "inss2.mm"
include "rexpssxrxp.mm"
include "sstri.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "funimass4.mm"
include "mp2an.mm"
include "sspwuni.mm"
include "sylib.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cres.mm"
include "cbl.mm"
include "co.mm"
include "crp.mm"
include "wrex.mm"
include "cxmt.mm"
include "eqid.mm"
include "rexmet.mm"
include "cmopn.mm"
include "tgioo.mm"
include "mopni2.mm"
include "mp3an1.mm"
include "caddc.mm"
include "wceq.mm"
include "elssuni.mm"
include "uniretop.mm"
include "syl6sseqr.mm"
include "sselda.mm"
include "rpre.mm"
include "bl2ioo.mm"
include "syl2an.mm"
include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "2re.mm"
include "1lt2.mm"
include "expnlbnd.mm"
include "mp3an23.mm"
include "ad2antrl.mm"
include "cmul.mm"
include "cfl.mm"
include "ad2antrr.mm"
include "2nn.mm"
include "nnnn0.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nnred.mm"
include "remulcld.mm"
include "fllelt.mm"
include "syl.mm"
include "simpld.mm"
include "cc0.mm"
include "reflcl.mm"
include "nngt0d.mm"
include "ledivmul2.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "peano2re.mm"
include "nndivred.mm"
include "simprd.mm"
include "ltmuldiv.mm"
include "mpbid.mm"
include "ltled.mm"
include "w3a.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbir3and.mm"
include "cop.mm"
include "flcld.mm"
include "dyadval.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eleqtrrd.mm"
include "wfn.mm"
include "ffn.mm"
include "fnovrn.mm"
include "simplrl.mm"
include "rpred.mm"
include "resubcld.mm"
include "rexrd.mm"
include "readdcld.mm"
include "recnd.mm"
include "1cnd.mm"
include "nnne0d.mm"
include "divdird.mm"
include "nnrecred.mm"
include "ltadd2dd.mm"
include "eqbrtrd.mm"
include "lttrd.mm"
include "ltsubaddd.mm"
include "leadd1dd.mm"
include "lelttrd.mm"
include "iccssioo.mm"
include "syl22anc.mm"
include "eqsstrd.mm"
include "simplrr.mm"
include "sstrd.mm"
include "sylanbrc.mm"
include "wi.mm"
include "funfvima2.mm"
include "elunii.mm"
include "rexlimddv.mm"
include "expr.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "equequ1.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "cbvrabv.mm"
include "a1i.mm"
include "dyadmbl.mm"
include "eqeltrrd.mm"

theorem opnmbllem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vw: setvar w
  let vz: setvar z
  let wph: wff ph
  let vi: setvar i
  let vr: setvar r
  let cD: class D
  let cG: class G
  assume dyadmbl.1: |- F = ( x e. ZZ , y e. NN0 |-> <. ( x / ( 2 ^ y ) ) , ( ( x + 1 ) / ( 2 ^ y ) ) >. )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint c d
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint d f
  disjoint d x
  disjoint d y
  disjoint f x
  disjoint f y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a t
  disjoint a w
  disjoint a z
  disjoint a ph
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b t
  disjoint b w
  disjoint b z
  disjoint b ph
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f w
  disjoint f z
  disjoint f ph
  disjoint m n
  disjoint m t
  disjoint m w
  disjoint m z
  disjoint m ph
  disjoint n t
  disjoint n w
  disjoint n z
  disjoint n ph
  disjoint t w
  disjoint t z
  disjoint ph t
  disjoint w z
  disjoint ph w
  disjoint ph z
  disjoint a i
  disjoint a r
  disjoint A a
  disjoint b i
  disjoint b r
  disjoint A b
  disjoint c i
  disjoint c m
  disjoint c n
  disjoint c r
  disjoint c t
  disjoint c w
  disjoint c z
  disjoint A c
  disjoint d i
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d t
  disjoint d w
  disjoint d z
  disjoint A d
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint i t
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint A i
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint D x
  disjoint D y
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G m
  disjoint G n
  disjoint G t
  disjoint G z
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F m
  disjoint F n
  disjoint F r
  disjoint F w
  disjoint F z
  assert |- ( A e. ( topGen ` ran (,) ) -> A e. dom vol )

  proof
    cA
    cioo
    crn
    ctg
    cfv
    #
    wcel
    #
    cicc
    vz
    cv
    #
    cicc
    cfv
    #
    cA
    wss
    #
    vz
    cF
    crn
    #
    crab
    #
    cima
    #
    cuni
    #
    cA
    cvol
    cdm
    @1
    @8
    cA
    @1
    @7
    cA
    cpw
    #
    wss
    #
    @8
    cA
    wss
    @1
    vw
    cv
    #
    cicc
    cfv
    #
    @9
    wcel
    #
    vw
    @6
    wral
    #
    @10
    @1
    @13
    vw
    @6
    @11
    @6
    wcel
    @1
    @11
    @5
    wcel
    #
    @12
    cA
    wss
    #
    wa
    #
    @13
    @4
    @16
    vz
    @11
    @5
    vz
    vw
    weq
    @3
    @12
    cA
    @2
    @11
    cicc
    fveq2
    sseq1d
    elrab
    @1
    @17
    wa
    @16
    @13
    @1
    @15
    @16
    simprr
    @12
    cA
    @11
    cicc
    fvex
    elpw
    sylibr
    sylan2b
    ralrimiva
    cicc
    wfun
    #
    @6
    cicc
    cdm
    #
    wss
    #
    @10
    @14
    wb
    cxr
    cxr
    cxp
    #
    cxr
    cpw
    #
    cicc
    wf
    @18
    iccf
    @21
    @22
    cicc
    ffun
    ax-mp
    #
    @6
    @21
    @19
    @6
    @5
    @21
    @4
    vz
    @5
    ssrab2
    #
    @5
    cle
    cr
    cr
    cxp
    #
    cin
    #
    @21
    cz
    cn0
    cxp
    #
    @26
    cF
    wf
    #
    @5
    @26
    wss
    vx
    vy
    cF
    dyadmbl.1
    dyadf
    #
    @27
    @26
    cF
    frn
    ax-mp
    @26
    @25
    @21
    cle
    @25
    inss2
    rexpssxrxp
    sstri
    sstri
    sstri
    @21
    @22
    cicc
    iccf
    fdmi
    sseqtr4i
    #
    vw
    @6
    @9
    cicc
    funimass4
    mp2an
    sylibr
    @7
    cA
    sspwuni
    sylib
    @1
    vw
    cA
    @8
    @1
    @11
    cA
    wcel
    #
    @11
    @8
    wcel
    #
    @1
    @31
    wa
    #
    @11
    vr
    cv
    #
    cabs
    cmin
    ccom
    @25
    cres
    #
    cbl
    cfv
    co
    #
    cA
    wss
    #
    vr
    crp
    wrex
    #
    @32
    @35
    cr
    cxmt
    cfv
    wcel
    @1
    @31
    @38
    @35
    @35
    eqid
    #
    rexmet
    vr
    cA
    @35
    @11
    @0
    cr
    @35
    @35
    cmopn
    cfv
    #
    @39
    @40
    eqid
    tgioo
    mopni2
    mp3an1
    @33
    @37
    @32
    vr
    crp
    @33
    @34
    crp
    wcel
    #
    wa
    #
    @37
    @11
    @34
    cmin
    co
    #
    @11
    @34
    caddc
    co
    #
    cioo
    co
    #
    cA
    wss
    #
    @32
    @42
    @36
    @45
    cA
    @33
    @11
    cr
    wcel
    #
    @34
    cr
    wcel
    @36
    @45
    wceq
    @41
    @1
    cA
    cr
    @11
    @1
    cA
    @0
    cuni
    cr
    cA
    @0
    elssuni
    uniretop
    syl6sseqr
    sselda
    #
    @34
    rpre
    @11
    @34
    @35
    @39
    bl2ioo
    syl2an
    sseq1d
    @33
    @41
    @46
    @32
    @33
    @41
    @46
    wa
    #
    wa
    #
    c1
    c2
    vn
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    @34
    clt
    wbr
    #
    @32
    vn
    cn
    @41
    @54
    vn
    cn
    wrex
    #
    @33
    @46
    @41
    c2
    cr
    wcel
    c1
    c2
    clt
    wbr
    @55
    2re
    1lt2
    @34
    c2
    vn
    expnlbnd
    mp3an23
    ad2antrl
    @50
    @51
    cn
    wcel
    #
    @54
    wa
    #
    wa
    #
    @11
    @11
    @52
    cmul
    co
    #
    cfl
    cfv
    #
    @51
    cF
    co
    #
    cicc
    cfv
    #
    wcel
    @62
    @7
    wcel
    #
    @32
    @58
    @11
    @60
    @52
    cdiv
    co
    #
    @60
    c1
    caddc
    co
    #
    @52
    cdiv
    co
    #
    cicc
    co
    #
    @62
    @58
    @11
    @67
    wcel
    #
    @47
    @64
    @11
    cle
    wbr
    #
    @11
    @66
    cle
    wbr
    #
    @33
    @47
    @49
    @57
    @48
    ad2antrr
    #
    @58
    @69
    @60
    @59
    cle
    wbr
    #
    @58
    @72
    @59
    @65
    clt
    wbr
    #
    @58
    @59
    cr
    wcel
    #
    @72
    @73
    wa
    @58
    @11
    @52
    @71
    @58
    @52
    @58
    c2
    cn
    wcel
    @51
    cn0
    wcel
    #
    @52
    cn
    wcel
    2nn
    @56
    @75
    @50
    @54
    @51
    nnnn0
    ad2antrl
    #
    c2
    @51
    nnexpcl
    sylancr
    #
    nnred
    #
    remulcld
    #
    @59
    fllelt
    syl
    #
    simpld
    @58
    @60
    cr
    wcel
    #
    @47
    @52
    cr
    wcel
    #
    cc0
    @52
    clt
    wbr
    #
    @69
    @72
    wb
    @58
    @74
    @81
    @79
    @59
    reflcl
    syl
    #
    @71
    @78
    @58
    @52
    @77
    nngt0d
    #
    @60
    @11
    @52
    ledivmul2
    syl112anc
    mpbird
    #
    @58
    @11
    @66
    @71
    @58
    @65
    @52
    @58
    @81
    @65
    cr
    wcel
    #
    @84
    @60
    peano2re
    syl
    #
    @77
    nndivred
    #
    @58
    @73
    @11
    @66
    clt
    wbr
    #
    @58
    @72
    @73
    @80
    simprd
    @58
    @47
    @87
    @82
    @83
    @73
    @90
    wb
    @71
    @88
    @78
    @85
    @11
    @65
    @52
    ltmuldiv
    syl112anc
    mpbid
    #
    ltled
    @58
    @64
    cr
    wcel
    @66
    cr
    wcel
    @68
    @47
    @69
    @70
    w3a
    wb
    @58
    @60
    @52
    @84
    @77
    nndivred
    #
    @89
    @64
    @66
    @11
    elicc2
    syl2anc
    mpbir3and
    @58
    @62
    @64
    @66
    cop
    #
    cicc
    cfv
    @67
    @58
    @61
    @93
    cicc
    @58
    @60
    cz
    wcel
    #
    @75
    @61
    @93
    wceq
    @58
    @59
    @79
    flcld
    #
    @76
    vx
    vy
    @60
    @51
    cF
    dyadmbl.1
    dyadval
    syl2anc
    fveq2d
    @64
    @66
    cicc
    df-ov
    syl6eqr
    #
    eleqtrrd
    @58
    @61
    @6
    wcel
    #
    @63
    @58
    @61
    @5
    wcel
    #
    @62
    cA
    wss
    #
    @97
    @58
    @94
    @75
    @98
    @95
    @76
    cF
    @27
    wfn
    #
    @94
    @75
    @98
    @28
    @100
    @29
    @27
    @26
    cF
    ffn
    ax-mp
    cz
    cn0
    @60
    @51
    cF
    fnovrn
    mp3an1
    syl2anc
    @58
    @62
    @45
    cA
    @58
    @62
    @67
    @45
    @96
    @58
    @43
    cxr
    wcel
    @44
    cxr
    wcel
    @43
    @64
    clt
    wbr
    #
    @66
    @44
    clt
    wbr
    @67
    @45
    wss
    @58
    @43
    @58
    @11
    @34
    @71
    @58
    @34
    @33
    @41
    @46
    @57
    simplrl
    rpred
    #
    resubcld
    rexrd
    @58
    @44
    @58
    @11
    @34
    @71
    @102
    readdcld
    #
    rexrd
    @58
    @101
    @11
    @64
    @34
    caddc
    co
    #
    clt
    wbr
    @58
    @11
    @66
    @104
    @71
    @89
    @58
    @64
    @34
    @92
    @102
    readdcld
    @91
    @58
    @66
    @64
    @53
    caddc
    co
    #
    @104
    clt
    @58
    @60
    c1
    @52
    @58
    @60
    @84
    recnd
    @58
    1cnd
    @58
    @52
    @78
    recnd
    @58
    @52
    @77
    nnne0d
    divdird
    #
    @58
    @53
    @34
    @64
    @58
    @52
    @77
    nnrecred
    #
    @102
    @92
    @50
    @56
    @54
    simprr
    #
    ltadd2dd
    eqbrtrd
    lttrd
    @58
    @11
    @34
    @64
    @71
    @102
    @92
    ltsubaddd
    mpbird
    @58
    @66
    @11
    @53
    caddc
    co
    #
    @44
    @89
    @58
    @11
    @53
    @71
    @107
    readdcld
    @103
    @58
    @66
    @105
    @109
    cle
    @106
    @58
    @64
    @11
    @53
    @92
    @71
    @107
    @86
    leadd1dd
    eqbrtrd
    @58
    @53
    @34
    @11
    @107
    @102
    @71
    @108
    ltadd2dd
    lelttrd
    @43
    @44
    @64
    @66
    iccssioo
    syl22anc
    eqsstrd
    @33
    @41
    @46
    @57
    simplrr
    sstrd
    @4
    @99
    vz
    @61
    @5
    @2
    @61
    wceq
    @3
    @62
    cA
    @2
    @61
    cicc
    fveq2
    sseq1d
    elrab
    sylanbrc
    @18
    @20
    @97
    @63
    wi
    @23
    @30
    @6
    @61
    cicc
    funfvima2
    mp2an
    syl
    @11
    @62
    @7
    elunii
    syl2anc
    rexlimddv
    expr
    sylbid
    rexlimdva
    mpd
    ex
    ssrdv
    eqssd
    @1
    vx
    vy
    va
    vb
    @6
    cF
    vc
    cv
    #
    cicc
    cfv
    #
    vb
    cv
    cicc
    cfv
    #
    wss
    #
    vc
    vb
    weq
    #
    wi
    #
    vb
    @6
    wral
    #
    vc
    @6
    crab
    dyadmbl.1
    @116
    va
    cv
    #
    cicc
    cfv
    #
    @112
    wss
    #
    va
    vb
    weq
    #
    wi
    #
    vb
    @6
    wral
    vc
    va
    @6
    vc
    va
    weq
    #
    @115
    @121
    vb
    @6
    @122
    @113
    @119
    @114
    @120
    @122
    @111
    @118
    @112
    @110
    @117
    cicc
    fveq2
    sseq1d
    vc
    va
    vb
    equequ1
    imbi12d
    ralbidv
    cbvrabv
    @6
    @5
    wss
    @1
    @24
    a1i
    dyadmbl
    eqeltrrd
end
