include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "crp.mm"
include "wcel.mm"
include "cv.mm"
include "cvol.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "wrex.mm"
include "rphalfcld.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "wa.mm"
include "caddc.mm"
include "ccnv.mm"
include "cpnf.mm"
include "cioo.mm"
include "cima.mm"
include "cin.mm"
include "cdif.mm"
include "simprl.mm"
include "cmbf.mm"
include "wf.mm"
include "adantr.mm"
include "cico.mm"
include "wss.mm"
include "rge0ssre.mm"
include "fss.mm"
include "sylancl.mm"
include "mbfima.mm"
include "syl2anc.mm"
include "inmbl.mm"
include "difmbl.mm"
include "covol.mm"
include "wceq.mm"
include "c0.mm"
include "inass.mm"
include "disjdif.mm"
include "ineq2i.mm"
include "in0.mm"
include "3eqtri.mm"
include "fveq2i.mm"
include "ovol0.mm"
include "eqtri.mm"
include "a1i.mm"
include "cun.mm"
include "inundif.mm"
include "eqcomi.mm"
include "cicc.mm"
include "mblss.mm"
include "syl.mm"
include "sselda.mm"
include "cxr.mm"
include "cle.mm"
include "ffvelrnda.mm"
include "elrege0.mm"
include "sylib.mm"
include "simpld.mm"
include "rexrd.mm"
include "simprd.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "syldan.mm"
include "eqid.mm"
include "0e0iccpnf.mm"
include "ifcl.mm"
include "fmptd.mm"
include "cofr.mm"
include "icossicc.mm"
include "leidd.mm"
include "breq1.mm"
include "ifboth.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "reex.mm"
include "eqidd.mm"
include "feqmptd.mm"
include "ofrfval2.mm"
include "mpbird.mm"
include "itg2le.mm"
include "syl3anc.mm"
include "itg2lecl.mm"
include "itg2split.mm"
include "rpred.mm"
include "0red.mm"
include "elinel2.mm"
include "ifle.mm"
include "syl31anc.mm"
include "fveq2d.mm"
include "cmmbl.mm"
include "undif2.mm"
include "ssequn1.mm"
include "syl5req.mm"
include "iftrue.mm"
include "mpteq2ia.mm"
include "eqtrd.mm"
include "cmin.mm"
include "wn.mm"
include "wb.mm"
include "eldif.mm"
include "baib.mm"
include "adantl.mm"
include "wfn.mm"
include "ffnd.mm"
include "ad2antrr.mm"
include "elpreima.mm"
include "biantrurd.mm"
include "nnred.mm"
include "elioopnf.mm"
include "simpr.mm"
include "3bitr2d.mm"
include "ltnled.mm"
include "3bitr2rd.mm"
include "con1bid.mm"
include "bitrd.mm"
include "ifbid.mm"
include "mpteq2dva.mm"
include "breq1d.mm"
include "mtbird.mm"
include "resubcld.mm"
include "ltsubadd2d.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "ltadd1d.mm"
include "lelttrd.mm"
include "cmul.mm"
include "mblvol.mm"
include "simprr.mm"
include "ovolcl.mm"
include "xrltle.mm"
include "mpd.mm"
include "ovollecl.mm"
include "eqeltrd.mm"
include "remulcld.mm"
include "cn.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "eldifn.mm"
include "difssd.mm"
include "iftrued.mm"
include "3brtr4d.mm"
include "iffalse.mm"
include "0le0.mm"
include "breq2.mm"
include "eqbrtrd.mm"
include "pm2.61dan.mm"
include "ralrimivw.mm"
include "itg2const.mm"
include "breqtrd.mm"
include "nngt0d.mm"
include "ltmuldiv2.mm"
include "syl112anc.mm"
include "lt2addd.mm"
include "rpcnd.mm"
include "2halvesd.mm"
include "expr.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"

theorem itg2cnlem2
  let wph: wff ph
  let vx: setvar x
  let vu: setvar u
  let cC: class C
  let cF: class F
  let cM: class M
  let vd: setvar d
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  let vn: setvar n
  let vw: setvar w
  assume itg2cn.1: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume itg2cn.2: |- ( ph -> F e. MblFn )
  assume itg2cn.3: |- ( ph -> ( S.2 ` F ) e. RR )
  assume itg2cn.4: |- ( ph -> C e. RR+ )
  assume itg2cn.5: |- ( ph -> M e. NN )
  assume itg2cn.6: |- ( ph -> -. ( S.2 ` ( x e. RR |-> if ( ( F ` x ) <_ M , ( F ` x ) , 0 ) ) ) <_ ( ( S.2 ` F ) - ( C / 2 ) ) )

  disjoint d u
  disjoint d x
  disjoint C d
  disjoint u x
  disjoint C u
  disjoint C x
  disjoint F d
  disjoint F u
  disjoint F x
  disjoint ph u
  disjoint ph x
  disjoint M d
  disjoint M u
  disjoint M x
  disjoint d m
  disjoint d y
  disjoint d z
  disjoint m u
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint C m
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint d n
  disjoint d w
  disjoint m n
  disjoint m w
  disjoint F m
  disjoint n u
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint u w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint m ph
  disjoint n ph
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> E. d e. RR+ A. u e. dom vol ( ( vol ` u ) < d -> ( S.2 ` ( x e. RR |-> if ( x e. u , ( F ` x ) , 0 ) ) ) < C ) )

  proof
    wph
    cC
    c2
    cdiv
    co
    #
    cM
    cdiv
    co
    #
    crp
    wcel
    vu
    cv
    #
    cvol
    cfv
    #
    @1
    clt
    wbr
    #
    vx
    cr
    vx
    cv
    #
    @2
    wcel
    #
    @5
    cF
    cfv
    #
    cc0
    cif
    cmpt
    #
    citg2
    cfv
    #
    cC
    clt
    wbr
    #
    wi
    #
    vu
    cvol
    cdm
    #
    wral
    #
    @3
    vd
    cv
    #
    clt
    wbr
    #
    @10
    wi
    #
    vu
    @12
    wral
    #
    vd
    crp
    wrex
    wph
    @0
    cM
    wph
    cC
    itg2cn.4
    rphalfcld
    wph
    cM
    itg2cn.5
    nnrpd
    rpdivcld
    #
    wph
    @11
    vu
    @12
    wph
    @2
    @12
    wcel
    #
    @4
    @10
    wph
    @19
    @4
    wa
    #
    wa
    #
    @9
    @0
    @0
    caddc
    co
    #
    cC
    clt
    @21
    @9
    vx
    cr
    @5
    @2
    cF
    ccnv
    cM
    cpnf
    cioo
    co
    #
    cima
    #
    cin
    #
    wcel
    #
    @7
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    vx
    cr
    @5
    @2
    @24
    cdif
    #
    wcel
    #
    @7
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    caddc
    co
    @22
    clt
    @21
    vx
    @25
    @30
    @7
    @2
    @28
    @33
    @8
    @21
    @19
    @24
    @12
    wcel
    #
    @25
    @12
    wcel
    wph
    @19
    @4
    simprl
    #
    @21
    cF
    cmbf
    wcel
    #
    cr
    cr
    cF
    wf
    #
    @35
    wph
    @37
    @20
    itg2cn.2
    adantr
    wph
    @38
    @20
    wph
    cr
    cc0
    cpnf
    cico
    co
    #
    cF
    wf
    #
    @39
    cr
    wss
    @38
    itg2cn.1
    rge0ssre
    cr
    @39
    cr
    cF
    fss
    sylancl
    adantr
    cr
    cM
    cpnf
    cF
    mbfima
    syl2anc
    #
    @2
    @24
    inmbl
    syl2anc
    @21
    @19
    @35
    @30
    @12
    wcel
    @36
    @41
    @2
    @24
    difmbl
    syl2anc
    @25
    @30
    cin
    #
    covol
    cfv
    #
    cc0
    wceq
    @21
    @43
    c0
    covol
    cfv
    #
    cc0
    @42
    c0
    covol
    @42
    @2
    @24
    @30
    cin
    #
    cin
    @2
    c0
    cin
    c0
    @2
    @24
    @30
    inass
    @45
    c0
    @2
    @24
    @2
    disjdif
    ineq2i
    @2
    in0
    3eqtri
    fveq2i
    ovol0
    eqtri
    a1i
    @2
    @25
    @30
    cun
    #
    wceq
    @21
    @46
    @2
    @2
    @24
    inundif
    eqcomi
    a1i
    @21
    @6
    @5
    cr
    wcel
    #
    @7
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @21
    @2
    cr
    @5
    @21
    @19
    @2
    cr
    wss
    #
    @36
    @2
    mblss
    syl
    #
    sselda
    #
    @21
    @47
    wa
    #
    @7
    cxr
    wcel
    cc0
    @7
    cle
    wbr
    #
    @49
    @53
    @7
    @53
    @7
    cr
    wcel
    #
    @54
    @53
    @7
    @39
    wcel
    @55
    @54
    wa
    @21
    cr
    @39
    @5
    cF
    wph
    @40
    @20
    itg2cn.1
    adantr
    #
    ffvelrnda
    @7
    elrege0
    sylib
    #
    simpld
    #
    rexrd
    @53
    @55
    @54
    @57
    simprd
    #
    @7
    elxrge0
    sylanbrc
    #
    syldan
    @28
    eqid
    #
    @33
    eqid
    #
    @8
    eqid
    @21
    cr
    @48
    @28
    wf
    #
    cF
    citg2
    cfv
    #
    cr
    wcel
    #
    @29
    @64
    cle
    wbr
    #
    @29
    cr
    wcel
    @21
    vx
    cr
    @27
    @48
    @28
    @53
    @49
    cc0
    @48
    wcel
    #
    @27
    @48
    wcel
    @60
    0e0iccpnf
    @26
    @7
    cc0
    @48
    ifcl
    sylancl
    #
    @61
    fmptd
    #
    wph
    @65
    @20
    itg2cn.3
    adantr
    #
    @21
    @63
    cr
    @48
    cF
    wf
    #
    @28
    cF
    cle
    cofr
    #
    wbr
    #
    @66
    @69
    @21
    @40
    @39
    @48
    wss
    @71
    @56
    cc0
    cpnf
    icossicc
    cr
    @39
    @48
    cF
    fss
    sylancl
    #
    @21
    @73
    @27
    @7
    cle
    wbr
    #
    vx
    cr
    wral
    @21
    @75
    vx
    cr
    @53
    @7
    @7
    cle
    wbr
    #
    @54
    @75
    @53
    @7
    @58
    leidd
    #
    @59
    @26
    @76
    @54
    @75
    @7
    cc0
    @7
    @27
    @7
    cle
    breq1
    cc0
    @27
    @7
    cle
    breq1
    ifboth
    syl2anc
    ralrimiva
    @21
    vx
    cr
    @27
    @7
    cle
    @28
    cF
    cvv
    @48
    cr
    cr
    cvv
    wcel
    @21
    reex
    a1i
    #
    @68
    @58
    @21
    @28
    eqidd
    #
    @21
    vx
    cr
    @39
    cF
    @56
    feqmptd
    #
    ofrfval2
    mpbird
    @28
    cF
    itg2le
    syl3anc
    @64
    @28
    itg2lecl
    syl3anc
    #
    @21
    cr
    @48
    @33
    wf
    #
    @65
    @34
    @64
    cle
    wbr
    #
    @34
    cr
    wcel
    @21
    vx
    cr
    @32
    @48
    @33
    @53
    @49
    @67
    @32
    @48
    wcel
    @60
    0e0iccpnf
    @31
    @7
    cc0
    @48
    ifcl
    sylancl
    #
    @62
    fmptd
    #
    @70
    @21
    @82
    @71
    @33
    cF
    @72
    wbr
    #
    @83
    @85
    @74
    @21
    @86
    @32
    @7
    cle
    wbr
    #
    vx
    cr
    wral
    @21
    @87
    vx
    cr
    @53
    @76
    @54
    @87
    @77
    @59
    @31
    @76
    @54
    @87
    @7
    cc0
    @7
    @32
    @7
    cle
    breq1
    cc0
    @32
    @7
    cle
    breq1
    ifboth
    syl2anc
    ralrimiva
    @21
    vx
    cr
    @32
    @7
    cle
    @33
    cF
    cvv
    @48
    cr
    @78
    @84
    @58
    @21
    @33
    eqidd
    #
    @80
    ofrfval2
    mpbird
    @33
    cF
    itg2le
    syl3anc
    @64
    @33
    itg2lecl
    syl3anc
    #
    itg2split
    @21
    @29
    @34
    @0
    @0
    @81
    @89
    @21
    @0
    @21
    cC
    wph
    cC
    crp
    wcel
    @20
    itg2cn.4
    adantr
    #
    rphalfcld
    rpred
    #
    @91
    @21
    @29
    vx
    cr
    @5
    @24
    wcel
    #
    @7
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    @0
    @81
    @21
    cr
    @48
    @94
    wf
    #
    @65
    @95
    @64
    cle
    wbr
    #
    @95
    cr
    wcel
    @21
    vx
    cr
    @93
    @48
    @94
    @53
    @49
    @67
    @93
    @48
    wcel
    @60
    0e0iccpnf
    @92
    @7
    cc0
    @48
    ifcl
    sylancl
    #
    @94
    eqid
    #
    fmptd
    #
    @70
    @21
    @96
    @71
    @94
    cF
    @72
    wbr
    #
    @97
    @100
    @74
    @21
    @101
    @93
    @7
    cle
    wbr
    #
    vx
    cr
    wral
    @21
    @102
    vx
    cr
    @53
    @76
    @54
    @102
    @77
    @59
    @92
    @76
    @54
    @102
    @7
    cc0
    @7
    @93
    @7
    cle
    breq1
    cc0
    @93
    @7
    cle
    breq1
    ifboth
    syl2anc
    ralrimiva
    @21
    vx
    cr
    @93
    @7
    cle
    @94
    cF
    cvv
    @48
    @48
    @78
    @98
    @60
    @21
    @94
    eqidd
    #
    @80
    ofrfval2
    mpbird
    @94
    cF
    itg2le
    syl3anc
    @64
    @94
    itg2lecl
    syl3anc
    #
    @91
    @21
    @63
    @96
    @28
    @94
    @72
    wbr
    #
    @29
    @95
    cle
    wbr
    @69
    @100
    @21
    @105
    @27
    @93
    cle
    wbr
    #
    vx
    cr
    wral
    @21
    @106
    vx
    cr
    @53
    @55
    cc0
    cr
    wcel
    @54
    @26
    @92
    wi
    #
    @106
    @58
    @53
    0red
    @59
    @107
    @53
    @5
    @2
    @24
    elinel2
    a1i
    @26
    @92
    @7
    cc0
    ifle
    syl31anc
    ralrimiva
    @21
    vx
    cr
    @27
    @93
    cle
    @28
    @94
    cvv
    @48
    @48
    @78
    @68
    @98
    @79
    @103
    ofrfval2
    mpbird
    @28
    @94
    itg2le
    syl3anc
    @21
    @95
    @0
    clt
    wbr
    @95
    vx
    cr
    @5
    cr
    @24
    cdif
    #
    wcel
    #
    @7
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    caddc
    co
    #
    @0
    @112
    caddc
    co
    #
    clt
    wbr
    @21
    @64
    @113
    @114
    clt
    @21
    @64
    vx
    cr
    @7
    cmpt
    #
    citg2
    cfv
    @113
    @21
    cF
    @115
    citg2
    @80
    fveq2d
    @21
    vx
    @24
    @108
    @7
    cr
    @94
    @111
    @115
    @41
    @21
    @35
    @108
    @12
    wcel
    @41
    @24
    cmmbl
    syl
    @24
    @108
    cin
    #
    covol
    cfv
    #
    cc0
    wceq
    @21
    @117
    @44
    cc0
    @116
    c0
    covol
    @24
    cr
    disjdif
    fveq2i
    ovol0
    eqtri
    a1i
    @21
    @24
    @108
    cun
    @24
    cr
    cun
    #
    cr
    @24
    cr
    undif2
    @21
    @24
    cr
    wss
    #
    @118
    cr
    wceq
    @21
    @35
    @119
    @41
    @24
    mblss
    syl
    @24
    cr
    ssequn1
    sylib
    syl5req
    @60
    @99
    @111
    eqid
    #
    vx
    cr
    @47
    @7
    cc0
    cif
    #
    cmpt
    @115
    vx
    cr
    @121
    @7
    @47
    @7
    cc0
    iftrue
    mpteq2ia
    eqcomi
    @104
    @21
    cr
    @48
    @111
    wf
    #
    @65
    @112
    @64
    cle
    wbr
    #
    @112
    cr
    wcel
    @21
    vx
    cr
    @110
    @48
    @111
    @53
    @49
    @67
    @110
    @48
    wcel
    @60
    0e0iccpnf
    @109
    @7
    cc0
    @48
    ifcl
    sylancl
    #
    @120
    fmptd
    #
    @70
    @21
    @122
    @71
    @111
    cF
    @72
    wbr
    #
    @123
    @125
    @74
    @21
    @126
    @110
    @7
    cle
    wbr
    #
    vx
    cr
    wral
    @21
    @127
    vx
    cr
    @53
    @76
    @54
    @127
    @77
    @59
    @109
    @76
    @54
    @127
    @7
    cc0
    @7
    @110
    @7
    cle
    breq1
    cc0
    @110
    @7
    cle
    breq1
    ifboth
    syl2anc
    ralrimiva
    @21
    vx
    cr
    @110
    @7
    cle
    @111
    cF
    cvv
    @48
    @48
    @78
    @124
    @60
    @21
    @111
    eqidd
    @80
    ofrfval2
    mpbird
    @111
    cF
    itg2le
    syl3anc
    @64
    @111
    itg2lecl
    syl3anc
    #
    itg2split
    eqtrd
    @21
    @64
    @0
    cmin
    co
    #
    @112
    clt
    wbr
    #
    @64
    @114
    clt
    wbr
    @21
    @130
    @112
    @129
    cle
    wbr
    #
    wn
    @21
    @131
    vx
    cr
    @7
    cM
    cle
    wbr
    #
    @7
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    @129
    cle
    wbr
    #
    wph
    @136
    wn
    @20
    itg2cn.6
    adantr
    @21
    @112
    @135
    @129
    cle
    @21
    @111
    @134
    citg2
    @21
    vx
    cr
    @110
    @133
    @53
    @109
    @132
    @7
    cc0
    @53
    @109
    @92
    wn
    #
    @132
    @47
    @109
    @137
    wb
    @21
    @109
    @47
    @137
    @5
    cr
    @24
    eldif
    baib
    adantl
    @53
    @132
    @92
    @53
    @92
    @47
    @7
    @23
    wcel
    #
    wa
    #
    cM
    @7
    clt
    wbr
    #
    @132
    wn
    #
    @53
    cF
    cr
    wfn
    #
    @92
    @139
    wb
    wph
    @142
    @20
    @47
    wph
    cr
    @39
    cF
    itg2cn.1
    ffnd
    ad2antrr
    cr
    @5
    @23
    cF
    elpreima
    syl
    @53
    @140
    @55
    @140
    wa
    #
    @138
    @139
    @53
    @55
    @140
    @58
    biantrurd
    @53
    cM
    cxr
    wcel
    #
    @138
    @143
    wb
    @53
    cM
    wph
    cM
    cr
    wcel
    #
    @20
    @47
    wph
    cM
    itg2cn.5
    nnred
    #
    ad2antrr
    #
    rexrd
    cM
    @7
    elioopnf
    syl
    @53
    @47
    @138
    @21
    @47
    simpr
    biantrurd
    3bitr2d
    @53
    cM
    @7
    @147
    @58
    ltnled
    3bitr2rd
    #
    con1bid
    bitrd
    ifbid
    mpteq2dva
    fveq2d
    breq1d
    mtbird
    @21
    @129
    @112
    @21
    @64
    @0
    @70
    @91
    resubcld
    @128
    ltnled
    mpbird
    @21
    @64
    @0
    @112
    @70
    @91
    @128
    ltsubadd2d
    mpbid
    eqbrtrrd
    @21
    @95
    @0
    @112
    @104
    @91
    @128
    ltadd1d
    mpbird
    lelttrd
    @21
    @34
    cM
    @3
    cmul
    co
    #
    @0
    @89
    @21
    cM
    @3
    wph
    @145
    @20
    @146
    adantr
    #
    @21
    @3
    @2
    covol
    cfv
    #
    cr
    @21
    @19
    @3
    @151
    wceq
    @36
    @2
    mblvol
    syl
    #
    @21
    @50
    @1
    cr
    wcel
    #
    @151
    @1
    cle
    wbr
    #
    @151
    cr
    wcel
    @51
    wph
    @153
    @20
    wph
    @1
    @18
    rpred
    adantr
    #
    @21
    @151
    @1
    clt
    wbr
    #
    @154
    @21
    @3
    @151
    @1
    clt
    @152
    wph
    @19
    @4
    simprr
    #
    eqbrtrrd
    @21
    @151
    cxr
    wcel
    #
    @1
    cxr
    wcel
    @156
    @154
    wi
    @21
    @50
    @158
    @51
    @2
    ovolcl
    syl
    @21
    @1
    @155
    rexrd
    @151
    @1
    xrltle
    syl2anc
    mpd
    @2
    @1
    ovollecl
    syl3anc
    eqeltrd
    #
    remulcld
    @91
    @21
    @34
    vx
    cr
    @6
    cM
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    @149
    cle
    @21
    @82
    cr
    @48
    @161
    wf
    @33
    @161
    @72
    wbr
    #
    @34
    @162
    cle
    wbr
    @85
    @21
    vx
    cr
    @160
    @48
    @161
    @21
    @160
    @48
    wcel
    #
    @47
    @21
    cM
    @48
    wcel
    #
    @67
    @164
    @21
    @144
    cc0
    cM
    cle
    wbr
    #
    @165
    @21
    cM
    @150
    rexrd
    @21
    cM
    @21
    cM
    wph
    cM
    cn
    wcel
    @20
    itg2cn.5
    adantr
    #
    nnnn0d
    nn0ge0d
    #
    cM
    elxrge0
    sylanbrc
    0e0iccpnf
    @6
    cM
    cc0
    @48
    ifcl
    sylancl
    adantr
    #
    @161
    eqid
    fmptd
    @21
    @163
    @32
    @160
    cle
    wbr
    #
    vx
    cr
    wral
    @21
    @170
    vx
    cr
    @21
    @31
    @170
    @21
    @31
    wa
    #
    @7
    cM
    @32
    @160
    cle
    @171
    @137
    @132
    @31
    @137
    @21
    @5
    @2
    @24
    eldifn
    adantl
    @171
    @132
    @92
    @21
    @31
    @6
    @141
    @92
    wb
    #
    @21
    @30
    @2
    @5
    @21
    @2
    @24
    difssd
    sselda
    #
    @21
    @6
    @47
    @172
    @52
    @148
    syldan
    syldan
    con1bid
    mpbid
    @31
    @32
    @7
    wceq
    @21
    @31
    @7
    cc0
    iftrue
    adantl
    @171
    @6
    cM
    cc0
    @173
    iftrued
    3brtr4d
    @21
    @31
    wn
    #
    wa
    @32
    cc0
    @160
    cle
    @174
    @32
    cc0
    wceq
    @21
    @31
    @7
    cc0
    iffalse
    adantl
    @21
    cc0
    @160
    cle
    wbr
    #
    @174
    @21
    @166
    cc0
    cc0
    cle
    wbr
    #
    @175
    @168
    0le0
    @6
    @166
    @176
    @175
    cM
    cc0
    cM
    @160
    cc0
    cle
    breq2
    cc0
    @160
    cc0
    cle
    breq2
    ifboth
    sylancl
    adantr
    eqbrtrd
    pm2.61dan
    ralrimivw
    @21
    vx
    cr
    @32
    @160
    cle
    @33
    @161
    cvv
    @48
    @48
    @78
    @84
    @169
    @88
    @21
    @161
    eqidd
    ofrfval2
    mpbird
    @33
    @161
    itg2le
    syl3anc
    @21
    @19
    @3
    cr
    wcel
    #
    cM
    @39
    wcel
    #
    @162
    @149
    wceq
    @36
    @159
    @21
    @145
    @166
    @178
    @150
    @168
    cM
    elrege0
    sylanbrc
    vx
    @2
    cM
    itg2const
    syl3anc
    breqtrd
    @21
    @149
    @0
    clt
    wbr
    #
    @4
    @157
    @21
    @177
    @0
    cr
    wcel
    @145
    cc0
    cM
    clt
    wbr
    @179
    @4
    wb
    @159
    @91
    @150
    @21
    cM
    @167
    nngt0d
    @3
    @0
    cM
    ltmuldiv2
    syl112anc
    mpbird
    lelttrd
    lt2addd
    eqbrtrd
    @21
    cC
    @21
    cC
    @90
    rpcnd
    2halvesd
    breqtrd
    expr
    ralrimiva
    @17
    @13
    vd
    @1
    crp
    @14
    @1
    wceq
    #
    @16
    @11
    vu
    @12
    @180
    @15
    @4
    @10
    @14
    @1
    @3
    clt
    breq2
    imbi1d
    ralbidv
    rspcev
    syl2anc
end
