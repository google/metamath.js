include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "clgs.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cif.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "cseq.mm"
include "cdvds.mm"
include "c8.mm"
include "cmo.mm"
include "c7.mm"
include "cpr.mm"
include "cmin.mm"
include "cdiv.mm"
include "caddc.mm"
include "prmz.mm"
include "lgsval.mm"
include "sylan2.mm"
include "cn.mm"
include "prmnn.mm"
include "adantl.mm"
include "nnne0d.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "cle.mm"
include "wn.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "cr.mm"
include "wb.mm"
include "0re.mm"
include "nnred.mm"
include "lenlt.mm"
include "sylancr.mm"
include "mpbid.mm"
include "intnanrd.mm"
include "absidd.mm"
include "fveq2d.mm"
include "cuz.mm"
include "1z.mm"
include "prmuz2.mm"
include "df-2.mm"
include "fveq2i.mm"
include "syl6eleq.mm"
include "seqm1.mm"
include "1t1e1.mm"
include "a1i.mm"
include "uz2m1nn.mm"
include "syl.mm"
include "nnuz.mm"
include "cv.mm"
include "cfz.mm"
include "cpc.mm"
include "elfznn.mm"
include "lgsfval.mm"
include "elfzelz.mm"
include "zred.mm"
include "ltm1d.mm"
include "elfzle2.mm"
include "peano2rem.mm"
include "lenltd.mm"
include "pm2.65i.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "con2i.mm"
include "ad2antlr.mm"
include "simpllr.mm"
include "dvdsprm.mm"
include "syl2anc.mm"
include "mtbird.mm"
include "simpr.mm"
include "ad2antrr.mm"
include "pceq0.mm"
include "mpbird.mm"
include "oveq2d.mm"
include "cc.mm"
include "0z.mm"
include "neg1z.mm"
include "keepel.mm"
include "cn0.mm"
include "simpl.mm"
include "csn.mm"
include "cdif.mm"
include "wne.mm"
include "simplr.mm"
include "neqned.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "oddprm.mm"
include "zexpcl.mm"
include "peano2zd.mm"
include "zmodcld.mm"
include "nn0zd.mm"
include "peano2zm.mm"
include "ifclda.mm"
include "zcnd.mm"
include "adantlr.mm"
include "exp0d.mm"
include "eqtrd.mm"
include "ifeq1da.mm"
include "ifid.mm"
include "syl6eq.mm"
include "seqid3.mm"
include "oveq1d.mm"
include "wf.mm"
include "lgsfcl.mm"
include "syl3anc.mm"
include "ffvelrnd.mm"
include "mulid2d.mm"
include "3eqtrd.mm"
include "oveq12d.mm"
include "iftrue.mm"
include "nncnd.mm"
include "exp1d.mm"
include "pcid.mm"
include "sylancl.mm"
include "eqtr3d.mm"
include "wral.mm"
include "ralrimiva.mm"
include "eqeq1.mm"
include "oveq1.mm"
include "id.mm"
include "ifbieq2d.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"

theorem lgsval2lem
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let cZ: class Z
  assume lgsval.1: |- F = ( n e. NN |-> if ( n e. Prime , ( if ( n = 2 , if ( 2 || A , 0 , if ( ( A mod 8 ) e. { 1 , 7 } , 1 , -u 1 ) ) , ( ( ( ( A ^ ( ( n - 1 ) / 2 ) ) + 1 ) mod n ) - 1 ) ) ^ ( n pCnt N ) ) , 1 ) )

  disjoint A n
  disjoint N n
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F a
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint M n
  disjoint M x
  disjoint N a
  disjoint N m
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Z a
  disjoint Z b
  disjoint Z n
  disjoint Z y
  disjoint Z z
  assert |- ( ( A e. ZZ /\ N e. Prime ) -> ( A /L N ) = if ( N = 2 , if ( 2 || A , 0 , if ( ( A mod 8 ) e. { 1 , 7 } , 1 , -u 1 ) ) , ( ( ( ( A ^ ( ( N - 1 ) / 2 ) ) + 1 ) mod N ) - 1 ) ) )

  proof
    cA
    cz
    wcel
    #
    cN
    cprime
    wcel
    #
    wa
    #
    cA
    cN
    clgs
    co
    #
    cN
    cc0
    wceq
    #
    cA
    c2
    cexp
    co
    c1
    wceq
    c1
    cc0
    cif
    #
    cN
    cc0
    clt
    wbr
    #
    cA
    cc0
    clt
    wbr
    #
    wa
    #
    c1
    cneg
    #
    c1
    cif
    #
    cN
    cabs
    cfv
    #
    cmul
    cF
    c1
    cseq
    #
    cfv
    #
    cmul
    co
    #
    cif
    #
    @14
    cN
    c2
    wceq
    #
    c2
    cA
    cdvds
    wbr
    #
    cc0
    cA
    c8
    cmo
    co
    c1
    c7
    cpr
    wcel
    #
    c1
    @9
    cif
    #
    cif
    #
    cA
    cN
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    cN
    cmo
    co
    #
    c1
    cmin
    co
    #
    cif
    #
    @1
    @0
    cN
    cz
    wcel
    #
    @3
    @15
    wceq
    cN
    prmz
    #
    cA
    vn
    cF
    cN
    lgsval.1
    lgsval
    sylan2
    @2
    @4
    @5
    @14
    @2
    cN
    cc0
    @2
    cN
    @1
    cN
    cn
    wcel
    #
    @0
    cN
    prmnn
    adantl
    #
    nnne0d
    #
    neneqd
    iffalsed
    @2
    @14
    c1
    cN
    cF
    cfv
    #
    cmul
    co
    #
    @33
    @27
    @2
    @10
    c1
    @13
    @33
    cmul
    @2
    @8
    @9
    c1
    @2
    @6
    @7
    @2
    cc0
    cN
    cle
    wbr
    #
    @6
    wn
    #
    @2
    cN
    @2
    cN
    @31
    nnnn0d
    nn0ge0d
    #
    @2
    cc0
    cr
    wcel
    cN
    cr
    wcel
    #
    @35
    @36
    wb
    0re
    @2
    cN
    @31
    nnred
    #
    cc0
    cN
    lenlt
    sylancr
    mpbid
    intnanrd
    iffalsed
    @2
    @13
    cN
    @12
    cfv
    #
    @33
    @2
    @11
    cN
    @12
    @2
    cN
    @39
    @37
    absidd
    fveq2d
    @2
    @40
    @21
    @12
    cfv
    #
    @33
    cmul
    co
    #
    @34
    @33
    @2
    c1
    cz
    wcel
    #
    cN
    c1
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    @40
    @42
    wceq
    1z
    @2
    cN
    c2
    cuz
    cfv
    #
    @45
    @1
    cN
    @46
    wcel
    #
    @0
    cN
    prmuz2
    adantl
    #
    c2
    @44
    cuz
    df-2
    fveq2i
    syl6eleq
    cmul
    cF
    c1
    cN
    seqm1
    sylancr
    @2
    @41
    c1
    @33
    cmul
    @2
    vx
    cmul
    cF
    c1
    @21
    c1
    c1
    c1
    cmul
    co
    c1
    wceq
    @2
    1t1e1
    a1i
    @2
    @21
    cn
    c1
    cuz
    cfv
    @2
    @47
    @21
    cn
    wcel
    @48
    cN
    uz2m1nn
    syl
    nnuz
    syl6eleq
    @2
    vx
    cv
    #
    c1
    @21
    cfz
    co
    #
    wcel
    #
    wa
    #
    @49
    cF
    cfv
    #
    @49
    cprime
    wcel
    #
    @49
    c2
    wceq
    #
    @20
    cA
    @49
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    @49
    cmo
    co
    #
    c1
    cmin
    co
    #
    cif
    #
    @49
    cN
    cpc
    co
    #
    cexp
    co
    #
    c1
    cif
    #
    c1
    @52
    @49
    cn
    wcel
    #
    @53
    @65
    wceq
    @51
    @66
    @2
    @49
    @21
    elfznn
    adantl
    cA
    vn
    cF
    @49
    cN
    lgsval.1
    lgsfval
    syl
    @52
    @65
    @54
    c1
    c1
    cif
    c1
    @52
    @54
    @64
    c1
    c1
    @52
    @54
    wa
    #
    @64
    @62
    cc0
    cexp
    co
    c1
    @67
    @63
    cc0
    @62
    cexp
    @67
    @63
    cc0
    wceq
    #
    @49
    cN
    cdvds
    wbr
    #
    wn
    #
    @67
    @69
    @49
    cN
    wceq
    #
    @51
    @71
    wn
    @2
    @54
    @71
    @51
    @71
    @51
    cN
    @50
    wcel
    #
    @72
    @21
    cN
    clt
    wbr
    #
    @72
    cN
    @72
    cN
    cN
    c1
    @21
    elfzelz
    zred
    #
    ltm1d
    @72
    cN
    @21
    cle
    wbr
    @73
    wn
    cN
    c1
    @21
    elfzle2
    @72
    cN
    @21
    @74
    @72
    @38
    @21
    cr
    wcel
    @74
    cN
    peano2rem
    syl
    lenltd
    mpbid
    pm2.65i
    @49
    cN
    @50
    eleq1
    mtbiri
    con2i
    ad2antlr
    @67
    @49
    @46
    wcel
    #
    @1
    @69
    @71
    wb
    @54
    @75
    @52
    @49
    prmuz2
    adantl
    @0
    @1
    @51
    @54
    simpllr
    cN
    @49
    dvdsprm
    syl2anc
    mtbird
    @67
    @54
    @30
    @68
    @70
    wb
    @52
    @54
    simpr
    @2
    @30
    @51
    @54
    @31
    ad2antrr
    @49
    cN
    pceq0
    syl2anc
    mpbird
    oveq2d
    @67
    @62
    @2
    @54
    @62
    cc
    wcel
    #
    @51
    @2
    @54
    wa
    #
    @62
    @77
    @55
    @20
    @61
    cz
    @20
    cz
    wcel
    @77
    @55
    wa
    @17
    cc0
    @19
    cz
    0z
    @18
    c1
    @9
    cz
    1z
    neg1z
    keepel
    keepel
    a1i
    @77
    @55
    wn
    #
    wa
    #
    @60
    cz
    wcel
    @61
    cz
    wcel
    @79
    @60
    @79
    @59
    @49
    @79
    @58
    @79
    @0
    @57
    cn0
    wcel
    @58
    cz
    wcel
    @2
    @0
    @54
    @78
    @0
    @1
    simpl
    #
    ad2antrr
    @79
    @57
    @79
    @49
    cprime
    c2
    csn
    cdif
    wcel
    #
    @57
    cn
    wcel
    @79
    @54
    @49
    c2
    wne
    @81
    @2
    @54
    @78
    simplr
    @79
    @49
    c2
    @77
    @78
    simpr
    neqned
    @49
    cprime
    c2
    eldifsn
    sylanbrc
    @49
    oddprm
    syl
    nnnn0d
    cA
    @57
    zexpcl
    syl2anc
    peano2zd
    @54
    @66
    @2
    @78
    @49
    prmnn
    ad2antlr
    zmodcld
    nn0zd
    @60
    peano2zm
    syl
    ifclda
    zcnd
    #
    adantlr
    exp0d
    eqtrd
    ifeq1da
    @54
    c1
    ifid
    syl6eq
    eqtrd
    seqid3
    oveq1d
    @2
    @33
    @2
    @33
    @2
    cn
    cz
    cN
    cF
    @2
    @0
    @28
    cN
    cc0
    wne
    cn
    cz
    cF
    wf
    @80
    @1
    @28
    @0
    @29
    adantl
    @32
    cA
    vn
    cF
    cN
    lgsval.1
    lgsfcl
    syl3anc
    @31
    ffvelrnd
    zcnd
    mulid2d
    #
    3eqtrd
    eqtrd
    oveq12d
    @83
    @2
    @33
    @1
    @27
    cN
    cN
    cpc
    co
    #
    cexp
    co
    #
    c1
    cif
    #
    @85
    @27
    @2
    @30
    @33
    @86
    wceq
    @31
    cA
    vn
    cF
    cN
    cN
    lgsval.1
    lgsfval
    syl
    @1
    @86
    @85
    wceq
    @0
    @1
    @85
    c1
    iftrue
    adantl
    @2
    @85
    @27
    c1
    cexp
    co
    @27
    @2
    @84
    c1
    @27
    cexp
    @2
    cN
    cN
    c1
    cexp
    co
    #
    cpc
    co
    #
    @84
    c1
    @2
    @87
    cN
    cN
    cpc
    @2
    cN
    @2
    cN
    @31
    nncnd
    exp1d
    oveq2d
    @2
    @1
    @43
    @88
    c1
    wceq
    @0
    @1
    simpr
    #
    1z
    c1
    cN
    pcid
    sylancl
    eqtr3d
    oveq2d
    @2
    @27
    @2
    @1
    @76
    vx
    cprime
    wral
    @27
    cc
    wcel
    #
    @89
    @2
    @76
    vx
    cprime
    @82
    ralrimiva
    @76
    @90
    vx
    cN
    cprime
    @71
    @62
    @27
    cc
    @71
    @55
    @16
    @61
    @26
    @20
    @49
    cN
    c2
    eqeq1
    @71
    @60
    @25
    c1
    cmin
    @71
    @59
    @24
    @49
    cN
    cmo
    @71
    @58
    @23
    c1
    caddc
    @71
    @57
    @22
    cA
    cexp
    @71
    @56
    @21
    c2
    cdiv
    @49
    cN
    c1
    cmin
    oveq1
    oveq1d
    oveq2d
    oveq1d
    @71
    id
    oveq12d
    oveq1d
    ifbieq2d
    eleq1d
    rspcv
    sylc
    exp1d
    eqtrd
    3eqtrd
    3eqtrd
    3eqtrd
end
