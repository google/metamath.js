include "cn.mm"
include "wcel.mm"
include "ccnv.mm"
include "cc0.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "csu.mm"
include "cdgr.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "ccoe.mm"
include "cdiv.mm"
include "cneg.mm"
include "cfz.mm"
include "cpi.mm"
include "cmul.mm"
include "ctan.mm"
include "c2.mm"
include "cexp.mm"
include "c6.mm"
include "cc.mm"
include "eqid.mm"
include "cply.mm"
include "wceq.mm"
include "cn0.mm"
include "cbc.mm"
include "cmpt.mm"
include "basellem2.mm"
include "simp1d.mm"
include "chash.mm"
include "simp2d.mm"
include "nnnn0.mm"
include "hashfz1.mm"
include "syl.mm"
include "cen.mm"
include "wbr.mm"
include "wf1o.mm"
include "basellem4.mm"
include "ovex.mm"
include "f1oen.mm"
include "cfn.mm"
include "wb.mm"
include "fzfid.mm"
include "cle.mm"
include "c0p.mm"
include "wne.mm"
include "wa.mm"
include "nnne0.mm"
include "eqnetrd.mm"
include "fveq2.mm"
include "dgr0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "fta1.mm"
include "syl2anc.mm"
include "simpld.mm"
include "hashen.mm"
include "mpbird.mm"
include "3eqtr2rd.mm"
include "id.mm"
include "eqeltrd.mm"
include "vieta1.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "fvmpt.mm"
include "adantl.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wf.mm"
include "plyf.mm"
include "fdm.mm"
include "3syl.mm"
include "syl5sseq.mm"
include "sselda.mm"
include "fsumf1o.mm"
include "simp3d.mm"
include "fveq12d.mm"
include "nnm1nn0.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "nncn.mm"
include "ax-1cn.mm"
include "nncan.mm"
include "sylancl.mm"
include "neg1cn.mm"
include "exp1.mm"
include "ax-mp.mm"
include "cz.mm"
include "caddc.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "mpan.mm"
include "peano2nnd.mm"
include "syl5eqel.mm"
include "nnnn0d.mm"
include "2z.mm"
include "nnz.mm"
include "peano2zm.mm"
include "zmulcl.mm"
include "sylancr.mm"
include "bccl.mm"
include "nn0cnd.mm"
include "mulcom.mm"
include "mulm1d.mm"
include "3eqtrd.mm"
include "negcld.mm"
include "subidd.mm"
include "exp0.mm"
include "cuz.mm"
include "wss.mm"
include "1eluzge0.mm"
include "fzss1.mm"
include "nnred.mm"
include "lep1d.mm"
include "syl6breqr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "nnzd.mm"
include "elfz5.mm"
include "sseldi.mm"
include "bccl2.mm"
include "nncnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "nnne0d.mm"
include "divnegd.mm"
include "negeqd.mm"
include "negnegd.mm"
include "c3.mm"
include "bcm1k.mm"
include "1cnd.mm"
include "pnncand.mm"
include "oveq1i.mm"
include "df-2.mm"
include "3eqtr4g.mm"
include "2nn0.mm"
include "syl6eqel.mm"
include "nn0sub.mm"
include "2timesd.mm"
include "addsubd.mm"
include "nn0nnaddcl.mm"
include "mpancom.mm"
include "2timesi.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "subsub4d.mm"
include "2cnd.mm"
include "subdid.mm"
include "3eqtr4a.mm"
include "subsubd.mm"
include "df-3.mm"
include "syl6eqr.mm"
include "cr.mm"
include "3re.mm"
include "nndivre.mm"
include "recnd.mm"
include "2re.mm"
include "mulassd.mm"
include "3cn.mm"
include "a1i.mm"
include "divmuldivd.mm"
include "3t2e6.mm"
include "mulcomd.mm"
include "6re.mm"
include "nnmulcld.mm"
include "eqeltrrd.mm"
include "nn0red.mm"
include "clt.mm"
include "ltm1d.mm"
include "eqbrtrrd.mm"
include "ltled.mm"
include "letrd.mm"
include "nn0uz.mm"
include "divcan3d.mm"
include "recdivd.mm"
include "6cn.mm"
include "6nn.mm"
include "nnne0i.mm"
include "recdiv.mm"
include "mpanl12.mm"
include "3eqtr3d.mm"

theorem basellem5
  let vt: setvar t
  let cP: class P
  let cT: class T
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vm: setvar m
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  assume basel.n: |- N = ( ( 2 x. M ) + 1 )
  assume basel.p: |- P = ( t e. CC |-> sum_ j e. ( 0 ... M ) ( ( ( N _C ( 2 x. j ) ) x. ( -u 1 ^ ( M - j ) ) ) x. ( t ^ j ) ) )
  assume basel.t: |- T = ( n e. ( 1 ... M ) |-> ( ( tan ` ( ( n x. _pi ) / N ) ) ^ -u 2 ) )

  disjoint j k
  disjoint j t
  disjoint k t
  disjoint j n
  disjoint M j
  disjoint k n
  disjoint M k
  disjoint n t
  disjoint M n
  disjoint M t
  disjoint N j
  disjoint N k
  disjoint N n
  disjoint N t
  disjoint P k
  disjoint P n
  disjoint T k
  disjoint j m
  disjoint A j
  disjoint k m
  disjoint A k
  disjoint m t
  disjoint A m
  disjoint A t
  disjoint j x
  disjoint j y
  disjoint k x
  disjoint k y
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
  disjoint N m
  disjoint N x
  disjoint P x
  disjoint T m
  disjoint T x
  disjoint T y
  assert |- ( M e. NN -> sum_ k e. ( 1 ... M ) ( ( tan ` ( ( k x. _pi ) / N ) ) ^ -u 2 ) = ( ( ( 2 x. M ) x. ( ( 2 x. M ) - 1 ) ) / 6 ) )

  proof
    cM
    cn
    wcel
    #
    cP
    ccnv
    cc0
    csn
    #
    cima
    #
    vx
    cv
    #
    vx
    csu
    cP
    cdgr
    cfv
    #
    c1
    cmin
    co
    #
    cP
    ccoe
    cfv
    #
    cfv
    #
    @4
    @6
    cfv
    #
    cdiv
    co
    cneg
    #
    c1
    cM
    cfz
    co
    #
    vk
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
    vk
    csu
    c2
    cM
    cmul
    co
    #
    @17
    c1
    cmin
    co
    #
    cmul
    co
    #
    c6
    cdiv
    co
    #
    @0
    vx
    @6
    @2
    cc
    cP
    @4
    @6
    eqid
    @4
    eqid
    @2
    eqid
    #
    @0
    cP
    cc
    cply
    cfv
    wcel
    #
    @4
    cM
    wceq
    #
    @6
    vn
    cn0
    cN
    c2
    vn
    cv
    #
    cmul
    co
    #
    cbc
    co
    #
    c1
    cneg
    #
    cM
    @24
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
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
    @0
    @4
    cM
    @10
    chash
    cfv
    #
    @2
    chash
    cfv
    #
    @0
    @22
    @23
    @32
    @33
    simp2d
    #
    @0
    cM
    cn0
    wcel
    #
    @35
    cM
    wceq
    cM
    nnnn0
    #
    cM
    hashfz1
    syl
    @0
    @35
    @36
    wceq
    #
    @10
    @2
    cen
    wbr
    #
    @0
    @10
    @2
    cT
    wf1o
    @41
    vt
    cP
    cT
    vj
    vn
    cM
    cN
    basel.n
    basel.p
    basel.t
    basellem4
    #
    @10
    @2
    cT
    c1
    cM
    cfz
    ovex
    f1oen
    syl
    @0
    @10
    cfn
    wcel
    @2
    cfn
    wcel
    #
    @40
    @41
    wb
    @0
    c1
    cM
    fzfid
    #
    @0
    @43
    @36
    @4
    cle
    wbr
    #
    @0
    @22
    cP
    c0p
    wne
    #
    @43
    @45
    wa
    @34
    @0
    @4
    cc0
    wne
    @46
    @0
    @4
    cM
    cc0
    @37
    cM
    nnne0
    eqnetrd
    cP
    c0p
    @4
    cc0
    cP
    c0p
    wceq
    @4
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
    @21
    fta1
    syl2anc
    simpld
    @10
    @2
    hashen
    syl2anc
    mpbird
    3eqtr2rd
    @0
    @4
    cM
    cn
    @37
    @0
    id
    eqeltrd
    vieta1
    @0
    @2
    @3
    @10
    @16
    vx
    vk
    cT
    @16
    @3
    @16
    wceq
    id
    @44
    @42
    @11
    @10
    wcel
    @11
    cT
    cfv
    @16
    wceq
    @0
    vn
    @11
    @24
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
    @15
    cexp
    co
    @16
    @10
    cT
    @24
    @11
    wceq
    #
    @49
    @14
    @15
    cexp
    @50
    @48
    @13
    ctan
    @50
    @47
    @12
    cN
    cdiv
    @24
    @11
    cpi
    cmul
    oveq1
    oveq1d
    fveq2d
    oveq1d
    basel.t
    @14
    @15
    cexp
    ovex
    fvmpt
    adantl
    @0
    @2
    cc
    @3
    @0
    cP
    cdm
    #
    @2
    cc
    cP
    @1
    cnvimass
    @0
    @22
    cc
    cc
    cP
    wf
    @51
    cc
    wceq
    @34
    cc
    cP
    plyf
    cc
    cc
    cP
    fdm
    3syl
    syl5sseq
    sselda
    fsumf1o
    @0
    @9
    @7
    cneg
    #
    @8
    cdiv
    co
    cN
    c2
    cM
    c1
    cmin
    co
    #
    cmul
    co
    #
    cbc
    co
    #
    cN
    @17
    cbc
    co
    #
    cdiv
    co
    #
    @20
    @0
    @7
    @8
    @0
    @7
    @55
    cneg
    #
    cc
    @0
    @7
    @53
    @31
    cfv
    #
    @55
    @27
    cM
    @53
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    @58
    @0
    @5
    @53
    @6
    @31
    @0
    @22
    @23
    @32
    @33
    simp3d
    #
    @0
    @4
    cM
    c1
    cmin
    @37
    oveq1d
    fveq12d
    @0
    @53
    cn0
    wcel
    #
    @59
    @62
    wceq
    cM
    nnm1nn0
    #
    vn
    @53
    @30
    @62
    cn0
    @31
    @24
    @53
    wceq
    #
    @26
    @55
    @29
    @61
    cmul
    @66
    @25
    @54
    cN
    cbc
    @24
    @53
    c2
    cmul
    oveq2
    oveq2d
    @66
    @28
    @60
    @27
    cexp
    @24
    @53
    cM
    cmin
    oveq2
    oveq2d
    oveq12d
    @31
    eqid
    #
    @55
    @61
    cmul
    ovex
    fvmpt
    syl
    @0
    @62
    @55
    @27
    cmul
    co
    #
    @27
    @55
    cmul
    co
    #
    @58
    @0
    @61
    @27
    @55
    cmul
    @0
    @61
    @27
    c1
    cexp
    co
    #
    @27
    @0
    @60
    c1
    @27
    cexp
    @0
    cM
    cc
    wcel
    c1
    cc
    wcel
    @60
    c1
    wceq
    cM
    nncn
    #
    ax-1cn
    cM
    c1
    nncan
    sylancl
    oveq2d
    @27
    cc
    wcel
    #
    @70
    @27
    wceq
    neg1cn
    @27
    exp1
    ax-mp
    syl6eq
    oveq2d
    @0
    @55
    cc
    wcel
    @72
    @68
    @69
    wceq
    @0
    @55
    @0
    cN
    cn0
    wcel
    #
    @54
    cz
    wcel
    #
    @55
    cn0
    wcel
    @0
    cN
    @0
    cN
    @17
    c1
    caddc
    co
    #
    cn
    basel.n
    @0
    @17
    c2
    cn
    wcel
    @0
    @17
    cn
    wcel
    #
    2nn
    c2
    cM
    nnmulcl
    mpan
    #
    peano2nnd
    syl5eqel
    #
    nnnn0d
    #
    @0
    c2
    cz
    wcel
    @53
    cz
    wcel
    #
    @74
    2z
    @0
    cM
    cz
    wcel
    @80
    cM
    nnz
    cM
    peano2zm
    syl
    c2
    @53
    zmulcl
    sylancr
    @54
    cN
    bccl
    syl2anc
    nn0cnd
    #
    neg1cn
    @55
    @27
    mulcom
    sylancl
    @0
    @55
    @81
    mulm1d
    3eqtrd
    3eqtrd
    #
    @0
    @55
    @81
    negcld
    eqeltrd
    @0
    @8
    @56
    cc
    @0
    @8
    cM
    @31
    cfv
    #
    @56
    @27
    cM
    cM
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    @56
    @0
    @4
    cM
    @6
    @31
    @63
    @37
    fveq12d
    @0
    @38
    @83
    @86
    wceq
    @39
    vn
    cM
    @30
    @86
    cn0
    @31
    @24
    cM
    wceq
    #
    @26
    @56
    @29
    @85
    cmul
    @87
    @25
    @17
    cN
    cbc
    @24
    cM
    c2
    cmul
    oveq2
    oveq2d
    @87
    @28
    @84
    @27
    cexp
    @24
    cM
    cM
    cmin
    oveq2
    oveq2d
    oveq12d
    @67
    @56
    @85
    cmul
    ovex
    fvmpt
    syl
    @0
    @86
    @56
    c1
    cmul
    co
    @56
    @0
    @85
    c1
    @56
    cmul
    @0
    @85
    @27
    cc0
    cexp
    co
    #
    c1
    @0
    @84
    cc0
    @27
    cexp
    @0
    cM
    @71
    subidd
    oveq2d
    @72
    @88
    c1
    wceq
    neg1cn
    @27
    exp0
    ax-mp
    syl6eq
    oveq2d
    @0
    @56
    @0
    @56
    @0
    @17
    cc0
    cN
    cfz
    co
    #
    wcel
    @56
    cn
    wcel
    @0
    c1
    cN
    cfz
    co
    #
    @89
    @17
    c1
    cc0
    cuz
    cfv
    #
    wcel
    @90
    @89
    wss
    1eluzge0
    c1
    cc0
    cN
    fzss1
    ax-mp
    @0
    @17
    @90
    wcel
    #
    @17
    cN
    cle
    wbr
    #
    @0
    @17
    @75
    cN
    cle
    @0
    @17
    @0
    @17
    @77
    nnred
    lep1d
    basel.n
    syl6breqr
    @0
    @17
    c1
    cuz
    cfv
    #
    wcel
    cN
    cz
    wcel
    #
    @92
    @93
    wb
    @0
    @17
    cn
    @94
    @77
    nnuz
    syl6eleq
    @0
    cN
    @78
    nnzd
    #
    @17
    c1
    cN
    elfz5
    syl2anc
    mpbird
    #
    sseldi
    @17
    cN
    bccl2
    syl
    #
    nncnd
    #
    mulid1d
    eqtrd
    3eqtrd
    #
    @99
    eqeltrd
    @0
    @8
    @56
    cc0
    @100
    @0
    @56
    @98
    nnne0d
    #
    eqnetrd
    divnegd
    @0
    @52
    @55
    @8
    @56
    cdiv
    @0
    @52
    @58
    cneg
    @55
    @0
    @7
    @58
    @82
    negeqd
    @0
    @55
    @81
    negnegd
    eqtrd
    @100
    oveq12d
    @0
    c1
    @56
    @55
    cdiv
    co
    #
    cdiv
    co
    c1
    c6
    @19
    cdiv
    co
    #
    cdiv
    co
    #
    @57
    @20
    @0
    @102
    @103
    c1
    cdiv
    @0
    @102
    @55
    @103
    cmul
    co
    #
    @55
    cdiv
    co
    @103
    @0
    @56
    @105
    @55
    cdiv
    @0
    @56
    @55
    c3
    @18
    cdiv
    co
    #
    c2
    @17
    cdiv
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    @105
    @0
    @56
    cN
    @18
    cbc
    co
    #
    cN
    @18
    cmin
    co
    #
    @17
    cdiv
    co
    #
    cmul
    co
    #
    @55
    @106
    cmul
    co
    #
    @107
    cmul
    co
    @109
    @0
    @92
    @56
    @113
    wceq
    @97
    @17
    cN
    bcm1k
    syl
    @0
    @110
    @114
    @112
    @107
    cmul
    @0
    @110
    cN
    @18
    c1
    cmin
    co
    #
    cbc
    co
    #
    cN
    @115
    cmin
    co
    #
    @18
    cdiv
    co
    #
    cmul
    co
    #
    @114
    @0
    @18
    @90
    wcel
    #
    @110
    @119
    wceq
    @0
    @120
    @18
    cN
    cle
    wbr
    #
    @0
    @121
    @111
    cn0
    wcel
    #
    @0
    @111
    c2
    cn0
    @0
    @75
    @18
    cmin
    co
    c1
    c1
    caddc
    co
    #
    @111
    c2
    @0
    @17
    c1
    c1
    @0
    @17
    @77
    nncnd
    #
    @0
    1cnd
    #
    @125
    pnncand
    cN
    @75
    @18
    cmin
    basel.n
    oveq1i
    df-2
    3eqtr4g
    #
    2nn0
    syl6eqel
    @0
    @18
    cn0
    wcel
    #
    @73
    @121
    @122
    wb
    @0
    @76
    @127
    @77
    @17
    nnm1nn0
    syl
    @79
    @18
    cN
    nn0sub
    syl2anc
    mpbird
    #
    @0
    @18
    @94
    wcel
    @95
    @120
    @121
    wb
    @0
    @18
    cn
    @94
    @0
    @18
    @53
    cM
    caddc
    co
    #
    cn
    @0
    @18
    cM
    cM
    caddc
    co
    #
    c1
    cmin
    co
    @129
    @0
    @17
    @130
    c1
    cmin
    @0
    cM
    @71
    2timesd
    oveq1d
    @0
    cM
    cM
    c1
    @71
    @71
    @125
    addsubd
    eqtrd
    @64
    @0
    @129
    cn
    wcel
    @65
    @53
    cM
    nn0nnaddcl
    mpancom
    eqeltrd
    #
    nnuz
    syl6eleq
    @96
    @18
    c1
    cN
    elfz5
    syl2anc
    mpbird
    @18
    cN
    bcm1k
    syl
    @0
    @116
    @55
    @118
    @106
    cmul
    @0
    @115
    @54
    cN
    cbc
    @0
    @17
    @123
    cmin
    co
    @17
    c2
    c1
    cmul
    co
    #
    cmin
    co
    @115
    @54
    @123
    @132
    @17
    cmin
    @132
    @123
    c1
    ax-1cn
    2timesi
    eqcomi
    oveq2i
    @0
    @17
    c1
    c1
    @124
    @125
    @125
    subsub4d
    @0
    c2
    cM
    c1
    @0
    2cnd
    #
    @71
    @125
    subdid
    3eqtr4a
    #
    oveq2d
    @0
    @117
    c3
    @18
    cdiv
    @0
    @117
    @111
    c1
    caddc
    co
    #
    c3
    @0
    cN
    @18
    c1
    @0
    cN
    @78
    nncnd
    @0
    @18
    @131
    nncnd
    #
    @125
    subsubd
    @0
    @135
    c2
    c1
    caddc
    co
    c3
    @0
    @111
    c2
    c1
    caddc
    @126
    oveq1d
    df-3
    syl6eqr
    eqtrd
    oveq1d
    oveq12d
    eqtrd
    @0
    @111
    c2
    @17
    cdiv
    @126
    oveq1d
    oveq12d
    @0
    @55
    @106
    @107
    @81
    @0
    @106
    @0
    c3
    cr
    wcel
    @18
    cn
    wcel
    #
    @106
    cr
    wcel
    3re
    @131
    c3
    @18
    nndivre
    sylancr
    recnd
    @0
    @107
    @0
    c2
    cr
    wcel
    @76
    @107
    cr
    wcel
    2re
    @77
    c2
    @17
    nndivre
    sylancr
    recnd
    mulassd
    3eqtrd
    @0
    @108
    @103
    @55
    cmul
    @0
    @108
    c3
    c2
    cmul
    co
    #
    @18
    @17
    cmul
    co
    #
    cdiv
    co
    @103
    @0
    c3
    @18
    c2
    @17
    c3
    cc
    wcel
    @0
    3cn
    a1i
    @136
    @133
    @124
    @0
    @18
    @131
    nnne0d
    @0
    @17
    @77
    nnne0d
    divmuldivd
    @0
    @138
    c6
    @139
    @19
    cdiv
    @138
    c6
    wceq
    @0
    3t2e6
    a1i
    @0
    @18
    @17
    @136
    @124
    mulcomd
    oveq12d
    eqtrd
    oveq2d
    eqtrd
    oveq1d
    @0
    @103
    @55
    @0
    @103
    @0
    c6
    cr
    wcel
    @19
    cn
    wcel
    @103
    cr
    wcel
    6re
    @0
    @17
    @18
    @77
    @131
    nnmulcld
    #
    c6
    @19
    nndivre
    sylancr
    recnd
    @81
    @0
    @55
    @0
    @54
    @89
    wcel
    #
    @55
    cn
    wcel
    @0
    @141
    @54
    cN
    cle
    wbr
    #
    @0
    @54
    @18
    cN
    @0
    @54
    @0
    @115
    @54
    cn0
    @134
    @0
    @137
    @115
    cn0
    wcel
    @131
    @18
    nnm1nn0
    syl
    eqeltrrd
    #
    nn0red
    #
    @0
    @18
    @131
    nnred
    #
    @0
    cN
    @78
    nnred
    @0
    @54
    @18
    @144
    @145
    @0
    @115
    @54
    @18
    clt
    @134
    @0
    @18
    @145
    ltm1d
    eqbrtrrd
    ltled
    @128
    letrd
    @0
    @54
    @91
    wcel
    @95
    @141
    @142
    wb
    @0
    @54
    cn0
    @91
    @143
    nn0uz
    syl6eleq
    @96
    @54
    cc0
    cN
    elfz5
    syl2anc
    mpbird
    @54
    cN
    bccl2
    syl
    nnne0d
    #
    divcan3d
    eqtrd
    oveq2d
    @0
    @56
    @55
    @99
    @81
    @101
    @146
    recdivd
    @0
    @19
    cc
    wcel
    #
    @19
    cc0
    wne
    #
    @104
    @20
    wceq
    #
    @0
    @19
    @140
    nncnd
    @0
    @19
    @140
    nnne0d
    c6
    cc
    wcel
    c6
    cc0
    wne
    @147
    @148
    wa
    @149
    6cn
    c6
    6nn
    nnne0i
    c6
    @19
    recdiv
    mpanl12
    syl2anc
    3eqtr3d
    3eqtrd
    3eqtr3d
end
