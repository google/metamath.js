include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "ccnv.mm"
include "cc0.mm"
include "csn.mm"
include "cima.mm"
include "wf1.mm"
include "wf1o.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "cpi.mm"
include "cmul.mm"
include "cdiv.mm"
include "ctan.mm"
include "c2.mm"
include "cneg.mm"
include "cexp.mm"
include "wa.mm"
include "cc.mm"
include "crp.mm"
include "cz.mm"
include "cioo.mm"
include "basellem1.mm"
include "tanrpcl.mm"
include "syl.mm"
include "2z.mm"
include "znegcl.mm"
include "ax-mp.mm"
include "rpexpcl.mm"
include "sylancl.mm"
include "rpcnd.mm"
include "csin.mm"
include "basellem3.mm"
include "syldan.mm"
include "cr.mm"
include "elfzelz.mm"
include "adantl.mm"
include "zred.mm"
include "pire.mm"
include "remulcl.mm"
include "recnd.mm"
include "caddc.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "mpan.mm"
include "peano2nnd.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan2d.mm"
include "fveq2d.mm"
include "sinkpi.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "nndivred.mm"
include "resincld.mm"
include "nnnn0d.mm"
include "expcld.mm"
include "clt.mm"
include "wbr.mm"
include "ccos.mm"
include "sincosq1sgn.mm"
include "simpld.mm"
include "gt0ne0d.mm"
include "nnzd.mm"
include "expne0d.mm"
include "div0d.mm"
include "3eqtrd.mm"
include "wfn.mm"
include "wb.mm"
include "cply.mm"
include "cdgr.mm"
include "ccoe.mm"
include "cn0.mm"
include "cbc.mm"
include "cmin.mm"
include "cmpt.mm"
include "basellem2.mm"
include "simp1d.mm"
include "plyf.mm"
include "ffn.mm"
include "3syl.mm"
include "fniniseg.mm"
include "mpbir2and.mm"
include "fmptd.mm"
include "fveq2.mm"
include "ssriv.mm"
include "rpred.mm"
include "ffvelrnda.mm"
include "simplr.mm"
include "sseli.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "a1i.mm"
include "pipos.mm"
include "ltmul1.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "ad2antrr.mm"
include "nnred.mm"
include "nngt0d.mm"
include "ltdiv1.mm"
include "cxr.mm"
include "cle.mm"
include "wss.mm"
include "neghalfpirx.mm"
include "pirp.mm"
include "rphalfcl.mm"
include "rpge0.mm"
include "mp2b.mm"
include "halfpire.mm"
include "le0neg2.mm"
include "mpbi.mm"
include "iooss1.mm"
include "mp2an.mm"
include "ad2ant2r.mm"
include "sseldi.mm"
include "ad2ant2rl.mm"
include "tanord.mm"
include "syl2anc.mm"
include "rprege0.mm"
include "lt2sq.mm"
include "syl2an.mm"
include "ltrecd.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt.mm"
include "2nn0.mm"
include "expneg.mm"
include "3brtr4d.mm"
include "an32s.mm"
include "ex.mm"
include "eqord2.mm"
include "biimprd.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "cen.mm"
include "cfn.mm"
include "cdom.mm"
include "chash.mm"
include "c0p.mm"
include "wne.mm"
include "simp2d.mm"
include "nnne0.mm"
include "eqnetrd.mm"
include "dgr0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "eqid.mm"
include "fta1.mm"
include "f1domg.mm"
include "sylc.mm"
include "simprd.mm"
include "nnnn0.mm"
include "hashfz1.mm"
include "eqtr4d.mm"
include "breqtrd.mm"
include "fzfid.mm"
include "hashdom.mm"
include "sbth.mm"
include "f1finf1o.mm"

theorem basellem4
  let vt: setvar t
  let cP: class P
  let cT: class T
  let vj: setvar j
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  assume basel.n: |- N = ( ( 2 x. M ) + 1 )
  assume basel.p: |- P = ( t e. CC |-> sum_ j e. ( 0 ... M ) ( ( ( N _C ( 2 x. j ) ) x. ( -u 1 ^ ( M - j ) ) ) x. ( t ^ j ) ) )
  assume basel.t: |- T = ( n e. ( 1 ... M ) |-> ( ( tan ` ( ( n x. _pi ) / N ) ) ^ -u 2 ) )

  disjoint j t
  disjoint j n
  disjoint M j
  disjoint n t
  disjoint M n
  disjoint M t
  disjoint N j
  disjoint N n
  disjoint N t
  disjoint P n
  disjoint j k
  disjoint j m
  disjoint A j
  disjoint k m
  disjoint k t
  disjoint A k
  disjoint m t
  disjoint A m
  disjoint A t
  disjoint j x
  disjoint j y
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint M k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint M m
  disjoint n x
  disjoint n y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint M x
  disjoint M y
  disjoint N k
  disjoint N m
  disjoint N x
  disjoint P k
  disjoint P x
  disjoint T k
  disjoint T m
  disjoint T x
  disjoint T y
  assert |- ( M e. NN -> T : ( 1 ... M ) -1-1-onto-> ( `' P " { 0 } ) )

  proof
    cM
    cn
    wcel
    #
    c1
    cM
    cfz
    co
    #
    cP
    ccnv
    cc0
    csn
    cima
    #
    cT
    wf1
    #
    @1
    @2
    cT
    wf1o
    #
    @0
    @1
    @2
    cT
    wf
    vx
    cv
    #
    cT
    cfv
    #
    vy
    cv
    #
    cT
    cfv
    #
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    @1
    wral
    vx
    @1
    wral
    @3
    @0
    vn
    @1
    vn
    cv
    #
    cpi
    cmul
    co
    #
    cN
    cdiv
    co
    #
    ctan
    cfv
    #
    c2
    cneg
    #
    cexp
    co
    #
    @2
    cT
    @0
    @12
    @1
    wcel
    #
    wa
    #
    @17
    @2
    wcel
    #
    @17
    cc
    wcel
    #
    @17
    cP
    cfv
    #
    cc0
    wceq
    #
    @19
    @17
    @19
    @15
    crp
    wcel
    #
    @16
    cz
    wcel
    #
    @17
    crp
    wcel
    @19
    @14
    cc0
    cpi
    c2
    cdiv
    co
    #
    cioo
    co
    #
    wcel
    #
    @24
    @12
    cM
    cN
    basel.n
    basellem1
    #
    @14
    tanrpcl
    syl
    c2
    cz
    wcel
    #
    @25
    2z
    c2
    znegcl
    ax-mp
    @15
    @16
    rpexpcl
    sylancl
    #
    rpcnd
    @19
    @22
    cN
    @14
    cmul
    co
    #
    csin
    cfv
    #
    @14
    csin
    cfv
    #
    cN
    cexp
    co
    #
    cdiv
    co
    #
    cc0
    @35
    cdiv
    co
    cc0
    @0
    @18
    @28
    @22
    @36
    wceq
    @29
    vt
    @14
    cP
    vj
    cM
    cN
    basel.n
    basel.p
    basellem3
    syldan
    @19
    @33
    cc0
    @35
    cdiv
    @19
    @33
    @13
    csin
    cfv
    #
    cc0
    @19
    @32
    @13
    csin
    @19
    @13
    cN
    @19
    @13
    @19
    @12
    cr
    wcel
    cpi
    cr
    wcel
    #
    @13
    cr
    wcel
    @19
    @12
    @18
    @12
    cz
    wcel
    #
    @0
    @12
    c1
    cM
    elfzelz
    #
    adantl
    #
    zred
    pire
    @12
    cpi
    remulcl
    sylancl
    #
    recnd
    @19
    cN
    @0
    cN
    cn
    wcel
    #
    @18
    @0
    cN
    c2
    cM
    cmul
    co
    #
    c1
    caddc
    co
    cn
    basel.n
    @0
    @44
    c2
    cn
    wcel
    @0
    @44
    cn
    wcel
    2nn
    c2
    cM
    nnmulcl
    mpan
    peano2nnd
    syl5eqel
    #
    adantr
    #
    nncnd
    @19
    cN
    @46
    nnne0d
    divcan2d
    fveq2d
    @19
    @39
    @37
    cc0
    wceq
    @41
    @12
    sinkpi
    syl
    eqtrd
    oveq1d
    @19
    @35
    @19
    @34
    cN
    @19
    @34
    @19
    @14
    @19
    @13
    cN
    @42
    @46
    nndivred
    resincld
    recnd
    #
    @19
    cN
    @46
    nnnn0d
    expcld
    @19
    @34
    cN
    @47
    @19
    @34
    @19
    cc0
    @34
    clt
    wbr
    #
    cc0
    @14
    ccos
    cfv
    clt
    wbr
    #
    @19
    @28
    @48
    @49
    wa
    @29
    @14
    sincosq1sgn
    syl
    simpld
    gt0ne0d
    @19
    cN
    @46
    nnzd
    expne0d
    div0d
    3eqtrd
    @19
    cP
    cc
    wfn
    #
    @20
    @21
    @23
    wa
    wb
    @0
    @50
    @18
    @0
    cP
    cc
    cply
    cfv
    wcel
    #
    cc
    cc
    cP
    wf
    @50
    @0
    @51
    cP
    cdgr
    cfv
    #
    cM
    wceq
    #
    cP
    ccoe
    cfv
    vn
    cn0
    cN
    c2
    @12
    cmul
    co
    cbc
    co
    c1
    cneg
    cM
    @12
    cmin
    co
    cexp
    co
    cmul
    co
    cmpt
    wceq
    #
    vt
    cP
    vj
    vn
    cM
    cN
    basel.n
    basel.p
    basellem2
    #
    simp1d
    #
    cc
    cP
    plyf
    cc
    cc
    cP
    ffn
    3syl
    adantr
    cc
    cc0
    @17
    cP
    fniniseg
    syl
    mpbir2and
    basel.t
    fmptd
    @0
    @11
    vx
    vy
    @1
    @1
    @0
    @5
    @1
    wcel
    @7
    @1
    wcel
    wa
    wa
    @10
    @9
    @0
    vk
    vm
    vk
    cv
    #
    cT
    cfv
    #
    vm
    cv
    #
    cT
    cfv
    #
    @5
    @7
    @1
    @6
    @8
    @57
    @59
    cT
    fveq2
    @57
    @5
    cT
    fveq2
    @57
    @7
    cT
    fveq2
    vn
    @1
    cr
    @18
    @12
    @40
    zred
    ssriv
    #
    @0
    @1
    cr
    @57
    cT
    @0
    vn
    @1
    @17
    cr
    cT
    @19
    @17
    @31
    rpred
    basel.t
    fmptd
    ffvelrnda
    @0
    @57
    @1
    wcel
    #
    @59
    @1
    wcel
    #
    wa
    #
    wa
    @57
    @59
    clt
    wbr
    #
    @60
    @58
    clt
    wbr
    #
    @0
    @65
    @64
    @66
    @0
    @65
    wa
    #
    @64
    wa
    #
    c1
    @59
    cpi
    cmul
    co
    #
    cN
    cdiv
    co
    #
    ctan
    cfv
    #
    c2
    cexp
    co
    #
    cdiv
    co
    #
    c1
    @57
    cpi
    cmul
    co
    #
    cN
    cdiv
    co
    #
    ctan
    cfv
    #
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @60
    @58
    clt
    @68
    @77
    @72
    clt
    wbr
    #
    @73
    @78
    clt
    wbr
    @68
    @76
    @71
    clt
    wbr
    #
    @79
    @68
    @75
    @70
    clt
    wbr
    #
    @80
    @68
    @74
    @69
    clt
    wbr
    #
    @81
    @68
    @65
    @82
    @0
    @65
    @64
    simplr
    @68
    @57
    cr
    wcel
    #
    @59
    cr
    wcel
    #
    @38
    cc0
    cpi
    clt
    wbr
    #
    @65
    @82
    wb
    @62
    @83
    @67
    @63
    @1
    cr
    @57
    @61
    sseli
    ad2antrl
    #
    @63
    @84
    @67
    @62
    @1
    cr
    @59
    @61
    sseli
    ad2antll
    #
    @38
    @68
    pire
    a1i
    @85
    @68
    pipos
    a1i
    @57
    @59
    cpi
    ltmul1
    syl112anc
    mpbid
    @68
    @74
    cr
    wcel
    #
    @69
    cr
    wcel
    #
    cN
    cr
    wcel
    cc0
    cN
    clt
    wbr
    @82
    @81
    wb
    @68
    @83
    @38
    @88
    @86
    pire
    @57
    cpi
    remulcl
    sylancl
    @68
    @84
    @38
    @89
    @87
    pire
    @59
    cpi
    remulcl
    sylancl
    @68
    cN
    @0
    @43
    @65
    @64
    @45
    ad2antrr
    #
    nnred
    @68
    cN
    @90
    nngt0d
    @74
    @69
    cN
    ltdiv1
    syl112anc
    mpbid
    @68
    @75
    @26
    cneg
    #
    @26
    cioo
    co
    #
    wcel
    @70
    @92
    wcel
    @81
    @80
    wb
    @68
    @27
    @92
    @75
    @91
    cxr
    wcel
    @91
    cc0
    cle
    wbr
    #
    @27
    @92
    wss
    neghalfpirx
    cc0
    @26
    cle
    wbr
    #
    @93
    cpi
    crp
    wcel
    @26
    crp
    wcel
    @94
    pirp
    cpi
    rphalfcl
    @26
    rpge0
    mp2b
    @26
    cr
    wcel
    @94
    @93
    wb
    halfpire
    @26
    le0neg2
    ax-mp
    mpbi
    @91
    cc0
    @26
    iooss1
    mp2an
    #
    @0
    @62
    @75
    @27
    wcel
    #
    @65
    @63
    @57
    cM
    cN
    basel.n
    basellem1
    ad2ant2r
    #
    sseldi
    @68
    @27
    @92
    @70
    @95
    @0
    @63
    @70
    @27
    wcel
    #
    @65
    @62
    @59
    cM
    cN
    basel.n
    basellem1
    ad2ant2rl
    #
    sseldi
    @75
    @70
    tanord
    syl2anc
    mpbid
    @68
    @76
    crp
    wcel
    #
    @71
    crp
    wcel
    #
    @80
    @79
    wb
    #
    @68
    @96
    @100
    @97
    @75
    tanrpcl
    syl
    #
    @68
    @98
    @101
    @99
    @70
    tanrpcl
    syl
    #
    @100
    @76
    cr
    wcel
    cc0
    @76
    cle
    wbr
    wa
    @71
    cr
    wcel
    cc0
    @71
    cle
    wbr
    wa
    @102
    @101
    @76
    rprege0
    @71
    rprege0
    @76
    @71
    lt2sq
    syl2an
    syl2anc
    mpbid
    @68
    @77
    @72
    @68
    @100
    @30
    @77
    crp
    wcel
    @103
    2z
    @76
    c2
    rpexpcl
    sylancl
    @68
    @101
    @30
    @72
    crp
    wcel
    @104
    2z
    @71
    c2
    rpexpcl
    sylancl
    ltrecd
    mpbid
    @68
    @60
    @71
    @16
    cexp
    co
    #
    @73
    @63
    @60
    @105
    wceq
    @67
    @62
    vn
    @59
    @17
    @105
    @1
    cT
    vn
    vm
    weq
    #
    @15
    @71
    @16
    cexp
    @106
    @14
    @70
    ctan
    @106
    @13
    @69
    cN
    cdiv
    @12
    @59
    cpi
    cmul
    oveq1
    oveq1d
    fveq2d
    oveq1d
    basel.t
    @71
    @16
    cexp
    ovex
    fvmpt
    ad2antll
    @68
    @71
    cc
    wcel
    c2
    cn0
    wcel
    #
    @105
    @73
    wceq
    @68
    @71
    @104
    rpcnd
    2nn0
    @71
    c2
    expneg
    sylancl
    eqtrd
    @68
    @58
    @76
    @16
    cexp
    co
    #
    @78
    @62
    @58
    @108
    wceq
    @67
    @63
    vn
    @57
    @17
    @108
    @1
    cT
    vn
    vk
    weq
    #
    @15
    @76
    @16
    cexp
    @109
    @14
    @75
    ctan
    @109
    @13
    @74
    cN
    cdiv
    @12
    @57
    cpi
    cmul
    oveq1
    oveq1d
    fveq2d
    oveq1d
    basel.t
    @76
    @16
    cexp
    ovex
    fvmpt
    ad2antrl
    @68
    @76
    cc
    wcel
    @107
    @108
    @78
    wceq
    @68
    @76
    @103
    rpcnd
    2nn0
    @76
    c2
    expneg
    sylancl
    eqtrd
    3brtr4d
    an32s
    ex
    eqord2
    biimprd
    ralrimivva
    vx
    vy
    @1
    @2
    cT
    dff13
    sylanbrc
    #
    @0
    @1
    @2
    cen
    wbr
    #
    @2
    cfn
    wcel
    #
    @3
    @4
    wb
    @0
    @1
    @2
    cdom
    wbr
    #
    @2
    @1
    cdom
    wbr
    #
    @111
    @0
    @112
    @3
    @113
    @0
    @112
    @2
    chash
    cfv
    #
    @52
    cle
    wbr
    #
    @0
    @51
    cP
    c0p
    wne
    #
    @112
    @116
    wa
    @56
    @0
    @52
    cc0
    wne
    @117
    @0
    @52
    cM
    cc0
    @0
    @51
    @53
    @54
    @55
    simp2d
    #
    cM
    nnne0
    eqnetrd
    cP
    c0p
    @52
    cc0
    cP
    c0p
    wceq
    @52
    c0p
    cdgr
    cfv
    cc0
    cP
    c0p
    cdgr
    fveq2
    dgr0
    syl6eq
    necon3i
    syl
    @2
    cc
    cP
    @2
    eqid
    fta1
    syl2anc
    #
    simpld
    #
    @110
    @1
    @2
    cfn
    cT
    f1domg
    sylc
    @0
    @115
    @1
    chash
    cfv
    #
    cle
    wbr
    #
    @114
    @0
    @115
    @52
    @121
    cle
    @0
    @112
    @116
    @119
    simprd
    @0
    @52
    cM
    @121
    @118
    @0
    cM
    cn0
    wcel
    @121
    cM
    wceq
    cM
    nnnn0
    cM
    hashfz1
    syl
    eqtr4d
    breqtrd
    @0
    @112
    @1
    cfn
    wcel
    @122
    @114
    wb
    @120
    @0
    c1
    cM
    fzfid
    @2
    @1
    cfn
    hashdom
    syl2anc
    mpbid
    @1
    @2
    sbth
    syl2anc
    @120
    @1
    @2
    cT
    f1finf1o
    syl2anc
    mpbid
end
