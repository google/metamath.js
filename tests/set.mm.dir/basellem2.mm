include "cn.mm"
include "wcel.mm"
include "cc.mm"
include "cply.mm"
include "cfv.mm"
include "cdgr.mm"
include "wceq.mm"
include "ccoe.mm"
include "cn0.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cbc.mm"
include "c1.mm"
include "cneg.mm"
include "cmin.mm"
include "cexp.mm"
include "cmpt.mm"
include "cc0.mm"
include "cfz.mm"
include "csu.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "nnnn0.mm"
include "wa.mm"
include "elfznn0.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "adantl.mm"
include "wf.mm"
include "cz.mm"
include "caddc.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "mpan.mm"
include "peano2nnd.mm"
include "syl5eqel.mm"
include "nnnn0d.mm"
include "2z.mm"
include "nn0z.mm"
include "zmulcl.mm"
include "sylancr.mm"
include "bccl.mm"
include "syl2an.mm"
include "nn0cnd.mm"
include "nnz.mm"
include "zsubcl.mm"
include "wne.mm"
include "neg1cn.mm"
include "neg1ne0.mm"
include "expclz.mm"
include "mp3an12.mm"
include "mulcld.mm"
include "fmptd.mm"
include "ffvelrn.mm"
include "eqeltrrd.mm"
include "elplyd.mm"
include "cuz.mm"
include "cima.mm"
include "csn.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wn.mm"
include "clt.mm"
include "cr.mm"
include "wb.mm"
include "nnre.mm"
include "nn0re.mm"
include "ltnle.mm"
include "ad2antlr.mm"
include "wo.mm"
include "ad2antrr.mm"
include "ax-1cn.mm"
include "2timesi.mm"
include "oveq2i.mm"
include "2cnd.mm"
include "nncn.mm"
include "adddid.mm"
include "oveq1i.mm"
include "nncnd.mm"
include "addassd.mm"
include "syl5eq.mm"
include "3eqtr4a.mm"
include "zltp1le.mm"
include "biimpa.mm"
include "peano2re.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "lemul2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "nnzd.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "olcd.mm"
include "bcval4.mm"
include "oveq1d.mm"
include "adantr.mm"
include "mul02d.mm"
include "3eqtrd.mm"
include "ex.mm"
include "sylbird.mm"
include "necon1ad.mm"
include "ralrimiva.mm"
include "plyco0.mm"
include "sumeq2i.mm"
include "mpteq2i.mm"
include "eqtr4i.mm"
include "subidd.mm"
include "exp0.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "nnred.mm"
include "lep1d.mm"
include "syl6breqr.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "elfz5.mm"
include "bccl2.mm"
include "mulid1d.mm"
include "nnne0d.mm"
include "eqnetrd.mm"
include "dgreq.mm"
include "coeeq.mm"
include "3jca.mm"

theorem basellem2
  let vt: setvar t
  let cP: class P
  let vj: setvar j
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  assume basel.n: |- N = ( ( 2 x. M ) + 1 )
  assume basel.p: |- P = ( t e. CC |-> sum_ j e. ( 0 ... M ) ( ( ( N _C ( 2 x. j ) ) x. ( -u 1 ^ ( M - j ) ) ) x. ( t ^ j ) ) )

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
  assert |- ( M e. NN -> ( P e. ( Poly ` CC ) /\ ( deg ` P ) = M /\ ( coeff ` P ) = ( n e. NN0 |-> ( ( N _C ( 2 x. n ) ) x. ( -u 1 ^ ( M - n ) ) ) ) ) )

  proof
    cM
    cn
    wcel
    #
    cP
    cc
    cply
    cfv
    #
    wcel
    cP
    cdgr
    cfv
    cM
    wceq
    cP
    ccoe
    cfv
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
    @2
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
    @0
    cP
    vt
    cc
    cc0
    cM
    cfz
    co
    #
    cN
    c2
    vj
    cv
    #
    cmul
    co
    #
    cbc
    co
    #
    @5
    cM
    @11
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    vt
    cv
    @11
    cexp
    co
    #
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    #
    @1
    basel.p
    @0
    vt
    @16
    cc
    vj
    cM
    cc
    cc
    wss
    @0
    cc
    ssid
    a1i
    cM
    nnnn0
    #
    @0
    @11
    @10
    wcel
    #
    wa
    @11
    @9
    cfv
    #
    @16
    cc
    @22
    @23
    @16
    wceq
    #
    @0
    @22
    @11
    cn0
    wcel
    #
    @24
    @11
    cM
    elfznn0
    #
    vn
    @11
    @8
    @16
    cn0
    @9
    @2
    @11
    wceq
    #
    @4
    @13
    @7
    @15
    cmul
    @27
    @3
    @12
    cN
    cbc
    @2
    @11
    c2
    cmul
    oveq2
    oveq2d
    @27
    @6
    @14
    @5
    cexp
    @2
    @11
    cM
    cmin
    oveq2
    oveq2d
    oveq12d
    @9
    eqid
    #
    @13
    @15
    cmul
    ovex
    fvmpt
    #
    syl
    #
    adantl
    @0
    cn0
    cc
    @9
    wf
    #
    @25
    @23
    cc
    wcel
    @22
    @0
    vn
    cn0
    @8
    cc
    @9
    @0
    @2
    cn0
    wcel
    #
    wa
    #
    @4
    @7
    @33
    @4
    @0
    cN
    cn0
    wcel
    #
    @3
    cz
    wcel
    #
    @4
    cn0
    wcel
    @32
    @0
    cN
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
    #
    cn
    basel.n
    @0
    @36
    c2
    cn
    wcel
    @0
    @36
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
    @32
    c2
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    @35
    2z
    @2
    nn0z
    #
    c2
    @2
    zmulcl
    sylancr
    @3
    cN
    bccl
    syl2an
    nn0cnd
    @33
    @6
    cz
    wcel
    #
    @7
    cc
    wcel
    #
    @0
    cM
    cz
    wcel
    #
    @43
    @45
    @32
    cM
    nnz
    #
    @44
    cM
    @2
    zsubcl
    syl2an
    @5
    cc
    wcel
    #
    @5
    cc0
    wne
    #
    @45
    @46
    neg1cn
    neg1ne0
    @5
    @6
    expclz
    mp3an12
    syl
    mulcld
    @28
    fmptd
    #
    @26
    cn0
    cc
    @11
    @9
    ffvelrn
    syl2an
    eqeltrrd
    elplyd
    syl5eqel
    #
    @0
    vt
    @9
    cc
    vj
    cP
    cM
    @52
    @21
    @51
    @0
    @9
    cM
    c1
    caddc
    co
    #
    cuz
    cfv
    cima
    cc0
    csn
    wceq
    #
    @23
    cc0
    wne
    @11
    cM
    cle
    wbr
    #
    wi
    #
    vj
    cn0
    wral
    #
    @0
    @56
    vj
    cn0
    @0
    @25
    wa
    #
    @55
    @23
    cc0
    @58
    @55
    wn
    #
    cM
    @11
    clt
    wbr
    #
    @23
    cc0
    wceq
    #
    @0
    cM
    cr
    wcel
    #
    @11
    cr
    wcel
    #
    @60
    @59
    wb
    @25
    cM
    nnre
    #
    @11
    nn0re
    #
    cM
    @11
    ltnle
    syl2an
    @58
    @60
    @61
    @58
    @60
    wa
    #
    @23
    @16
    cc0
    @15
    cmul
    co
    cc0
    @25
    @24
    @0
    @60
    @29
    ad2antlr
    @66
    @13
    cc0
    @15
    cmul
    @66
    @34
    @12
    cz
    wcel
    #
    @12
    cc0
    clt
    wbr
    #
    cN
    @12
    clt
    wbr
    #
    wo
    @13
    cc0
    wceq
    @0
    @34
    @25
    @60
    @41
    ad2antrr
    @66
    @42
    @11
    cz
    wcel
    #
    @67
    2z
    @25
    @70
    @0
    @60
    @11
    nn0z
    #
    ad2antlr
    c2
    @11
    zmulcl
    sylancr
    #
    @66
    @69
    @68
    @66
    @69
    cN
    c1
    caddc
    co
    #
    @12
    cle
    wbr
    #
    @66
    c2
    @53
    cmul
    co
    #
    @73
    @12
    cle
    @66
    @36
    c2
    c1
    cmul
    co
    #
    caddc
    co
    @36
    c1
    c1
    caddc
    co
    #
    caddc
    co
    #
    @75
    @73
    @76
    @77
    @36
    caddc
    c1
    ax-1cn
    2timesi
    oveq2i
    @66
    c2
    cM
    c1
    @66
    2cnd
    @0
    cM
    cc
    wcel
    @25
    @60
    cM
    nncn
    #
    ad2antrr
    c1
    cc
    wcel
    @66
    ax-1cn
    a1i
    #
    adddid
    @66
    @73
    @37
    c1
    caddc
    co
    @78
    cN
    @37
    c1
    caddc
    basel.n
    oveq1i
    @66
    @36
    c1
    c1
    @66
    @36
    @0
    @38
    @25
    @60
    @39
    ad2antrr
    nncnd
    @80
    @80
    addassd
    syl5eq
    3eqtr4a
    @66
    @53
    @11
    cle
    wbr
    #
    @75
    @12
    cle
    wbr
    #
    @58
    @60
    @81
    @0
    @47
    @70
    @60
    @81
    wb
    @25
    @48
    @71
    cM
    @11
    zltp1le
    syl2an
    biimpa
    @66
    @53
    cr
    wcel
    #
    @63
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @81
    @82
    wb
    @66
    @62
    @83
    @0
    @62
    @25
    @60
    @64
    ad2antrr
    cM
    peano2re
    syl
    @25
    @63
    @0
    @60
    @65
    ad2antlr
    @86
    @66
    @84
    @85
    2re
    2pos
    pm3.2i
    a1i
    @53
    @11
    c2
    lemul2
    syl3anc
    mpbid
    eqbrtrrd
    @66
    cN
    cz
    wcel
    #
    @67
    @69
    @74
    wb
    @0
    @87
    @25
    @60
    @0
    cN
    @40
    nnzd
    #
    ad2antrr
    @72
    cN
    @12
    zltp1le
    syl2anc
    mpbird
    olcd
    @12
    cN
    bcval4
    syl3anc
    oveq1d
    @66
    @15
    @58
    @15
    cc
    wcel
    #
    @60
    @58
    @14
    cz
    wcel
    #
    @89
    @0
    @47
    @70
    @90
    @25
    @48
    @71
    cM
    @11
    zsubcl
    syl2an
    @49
    @50
    @90
    @89
    neg1cn
    neg1ne0
    @5
    @14
    expclz
    mp3an12
    syl
    adantr
    mul02d
    3eqtrd
    ex
    sylbird
    necon1ad
    ralrimiva
    @0
    cM
    cn0
    wcel
    #
    @31
    @54
    @57
    wb
    @21
    @51
    @9
    vj
    cM
    plyco0
    syl2anc
    mpbird
    #
    cP
    vt
    cc
    @10
    @23
    @17
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    #
    wceq
    @0
    cP
    @20
    @95
    basel.p
    vt
    cc
    @94
    @19
    @10
    @93
    @18
    vj
    @22
    @23
    @16
    @17
    cmul
    @30
    oveq1d
    sumeq2i
    mpteq2i
    eqtr4i
    a1i
    #
    @0
    cM
    @9
    cfv
    #
    cN
    @36
    cbc
    co
    #
    cc0
    @0
    @97
    @98
    @5
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
    @98
    c1
    cmul
    co
    @98
    @0
    @91
    @97
    @101
    wceq
    @21
    vn
    cM
    @8
    @101
    cn0
    @9
    @2
    cM
    wceq
    #
    @4
    @98
    @7
    @100
    cmul
    @102
    @3
    @36
    cN
    cbc
    @2
    cM
    c2
    cmul
    oveq2
    oveq2d
    @102
    @6
    @99
    @5
    cexp
    @2
    cM
    cM
    cmin
    oveq2
    oveq2d
    oveq12d
    @28
    @98
    @100
    cmul
    ovex
    fvmpt
    syl
    @0
    @100
    c1
    @98
    cmul
    @0
    @100
    @5
    cc0
    cexp
    co
    #
    c1
    @0
    @99
    cc0
    @5
    cexp
    @0
    cM
    @79
    subidd
    oveq2d
    @49
    @103
    c1
    wceq
    neg1cn
    @5
    exp0
    ax-mp
    syl6eq
    oveq2d
    @0
    @98
    @0
    @98
    @0
    @36
    cc0
    cN
    cfz
    co
    wcel
    #
    @98
    cn
    wcel
    @0
    @104
    @36
    cN
    cle
    wbr
    #
    @0
    @36
    @37
    cN
    cle
    @0
    @36
    @0
    @36
    @39
    nnred
    lep1d
    basel.n
    syl6breqr
    @0
    @36
    cc0
    cuz
    cfv
    #
    wcel
    @87
    @104
    @105
    wb
    @0
    @36
    cn0
    @106
    @0
    @36
    @39
    nnnn0d
    nn0uz
    syl6eleq
    @88
    @36
    cc0
    cN
    elfz5
    syl2anc
    mpbird
    @36
    cN
    bccl2
    syl
    #
    nncnd
    mulid1d
    3eqtrd
    @0
    @98
    @107
    nnne0d
    eqnetrd
    dgreq
    @0
    vt
    @9
    cc
    vj
    cP
    cM
    @52
    @21
    @51
    @92
    @96
    coeeq
    3jca
end
