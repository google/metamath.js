include "wcel.mm"
include "cn.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "wceq.mm"
include "cfz.mm"
include "elfz1b.mm"
include "biimpi.mm"
include "eleq2s.mm"
include "3ancoma.mm"
include "sylibr.mm"
include "wa.mm"
include "df-3an.mm"
include "cv.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "wi.mm"
include "breq1.mm"
include "id.mm"
include "breq2.mm"
include "ifbid.mm"
include "ifeq12d.mm"
include "mpteq2dv.mm"
include "fveq2d.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "syl6eqr.mm"
include "cid.mm"
include "cres.mm"
include "cfn.mm"
include "fzfi.mm"
include "eqeltri.mm"
include "psgnid.mm"
include "ax-mp.mm"
include "eqid.mm"
include "fzto1st1.mm"
include "fveq2i.mm"
include "c2.mm"
include "1p1e2.mm"
include "oveq2i.mm"
include "neg1sqe1.mm"
include "eqtri.mm"
include "3eqtr4i.mm"
include "2a1i.mm"
include "cpr.mm"
include "cpmtr.mm"
include "ccom.mm"
include "cmul.mm"
include "simplr.mm"
include "peano2nnd.mm"
include "simpll.mm"
include "simpr.mm"
include "3jca.mm"
include "syl6eleqr.mm"
include "psgnfzto1stlem.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "a1i.mm"
include "crn.mm"
include "symgtrf.mm"
include "pmtrto1cl.mm"
include "sseldi.mm"
include "nnred.mm"
include "1red.mm"
include "readdcld.mm"
include "lep1d.mm"
include "letrd.mm"
include "fzto1st.mm"
include "syl.mm"
include "psgnco.mm"
include "syl3anc.mm"
include "psgnpmtr.mm"
include "mpd.mm"
include "oveq12d.mm"
include "cc.mm"
include "cn0.mm"
include "neg1cn.mm"
include "peano2nn.mm"
include "nnnn0d.mm"
include "expp1.mm"
include "sylancr.mm"
include "expcld.mm"
include "mulcomd.mm"
include "eqtr2d.mm"
include "ad3antlr.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "ex.mm"
include "nnindd.mm"
include "imp.mm"
include "sylbi.mm"

theorem psgnfzto1st
  let cB: class B
  let cD: class D
  let cP: class P
  let cS: class S
  let vi: setvar i
  let cG: class G
  let cI: class I
  let cN: class N
  let vx: setvar x
  let cK: class K
  let vm: setvar m
  let vn: setvar n
  assume psgnfzto1st.d: |- D = ( 1 ... N )
  assume psgnfzto1st.p: |- P = ( i e. D |-> if ( i = 1 , I , if ( i <_ I , ( i - 1 ) , i ) ) )
  assume psgnfzto1st.g: |- G = ( SymGrp ` D )
  assume psgnfzto1st.b: |- B = ( Base ` G )
  assume psgnfzto1st.s: |- S = ( pmSgn ` D )

  disjoint D i
  disjoint I i
  disjoint N i
  disjoint B i
  disjoint D x
  disjoint i x
  disjoint K i
  disjoint K x
  disjoint B m
  disjoint B n
  disjoint i m
  disjoint m n
  disjoint i n
  disjoint D m
  disjoint D n
  disjoint I m
  disjoint N m
  disjoint N n
  disjoint P m
  disjoint S m
  disjoint S n
  assert |- ( I e. D -> ( S ` P ) = ( -u 1 ^ ( I + 1 ) ) )

  proof
    cI
    cD
    wcel
    #
    cN
    cn
    wcel
    #
    cI
    cn
    wcel
    #
    cI
    cN
    cle
    wbr
    #
    w3a
    #
    cP
    cS
    cfv
    #
    c1
    cneg
    #
    cI
    c1
    caddc
    co
    #
    cexp
    co
    #
    wceq
    #
    @0
    @2
    @1
    @3
    w3a
    #
    @4
    @10
    cI
    c1
    cN
    cfz
    co
    #
    cD
    cI
    @11
    wcel
    @10
    cN
    cI
    elfz1b
    biimpi
    psgnfzto1st.d
    eleq2s
    @1
    @2
    @3
    3ancoma
    sylibr
    @4
    @1
    @2
    wa
    #
    @3
    wa
    @9
    @1
    @2
    @3
    df-3an
    @12
    @3
    @9
    @1
    vm
    cv
    #
    cN
    cle
    wbr
    #
    vi
    cD
    vi
    cv
    #
    c1
    wceq
    #
    @13
    @15
    @13
    cle
    wbr
    #
    @15
    c1
    cmin
    co
    #
    @15
    cif
    #
    cif
    #
    cmpt
    #
    cS
    cfv
    #
    @6
    @13
    c1
    caddc
    co
    #
    cexp
    co
    #
    wceq
    #
    wi
    c1
    cN
    cle
    wbr
    #
    vi
    cD
    @16
    c1
    @15
    c1
    cle
    wbr
    #
    @18
    @15
    cif
    #
    cif
    #
    cmpt
    #
    cS
    cfv
    #
    @6
    c1
    c1
    caddc
    co
    #
    cexp
    co
    #
    wceq
    #
    wi
    vn
    cv
    #
    cN
    cle
    wbr
    #
    vi
    cD
    @16
    @35
    @15
    @35
    cle
    wbr
    #
    @18
    @15
    cif
    #
    cif
    #
    cmpt
    #
    cS
    cfv
    #
    @6
    @35
    c1
    caddc
    co
    #
    cexp
    co
    #
    wceq
    #
    wi
    #
    @42
    cN
    cle
    wbr
    #
    vi
    cD
    @16
    @42
    @15
    @42
    cle
    wbr
    #
    @18
    @15
    cif
    #
    cif
    #
    cmpt
    #
    cS
    cfv
    #
    @6
    @42
    c1
    caddc
    co
    #
    cexp
    co
    #
    wceq
    #
    wi
    @3
    @9
    wi
    vm
    vn
    cI
    @13
    c1
    wceq
    #
    @14
    @26
    @25
    @34
    @13
    c1
    cN
    cle
    breq1
    @55
    @22
    @31
    @24
    @33
    @55
    @21
    @30
    cS
    @55
    vi
    cD
    @20
    @29
    @55
    @16
    @13
    c1
    @19
    @28
    @55
    id
    @55
    @17
    @27
    @18
    @15
    @13
    c1
    @15
    cle
    breq2
    ifbid
    ifeq12d
    mpteq2dv
    fveq2d
    @55
    @23
    @32
    @6
    cexp
    @13
    c1
    c1
    caddc
    oveq1
    oveq2d
    eqeq12d
    imbi12d
    @13
    @35
    wceq
    #
    @14
    @36
    @25
    @44
    @13
    @35
    cN
    cle
    breq1
    @56
    @22
    @41
    @24
    @43
    @56
    @21
    @40
    cS
    @56
    vi
    cD
    @20
    @39
    @56
    @16
    @13
    @35
    @19
    @38
    @56
    id
    @56
    @17
    @37
    @18
    @15
    @13
    @35
    @15
    cle
    breq2
    ifbid
    ifeq12d
    mpteq2dv
    fveq2d
    @56
    @23
    @42
    @6
    cexp
    @13
    @35
    c1
    caddc
    oveq1
    oveq2d
    eqeq12d
    imbi12d
    @13
    @42
    wceq
    #
    @14
    @46
    @25
    @54
    @13
    @42
    cN
    cle
    breq1
    @57
    @22
    @51
    @24
    @53
    @57
    @21
    @50
    cS
    @57
    vi
    cD
    @20
    @49
    @57
    @16
    @13
    @42
    @19
    @48
    @57
    id
    @57
    @17
    @47
    @18
    @15
    @13
    @42
    @15
    cle
    breq2
    ifbid
    ifeq12d
    mpteq2dv
    fveq2d
    @57
    @23
    @52
    @6
    cexp
    @13
    @42
    c1
    caddc
    oveq1
    oveq2d
    eqeq12d
    imbi12d
    @13
    cI
    wceq
    #
    @14
    @3
    @25
    @9
    @13
    cI
    cN
    cle
    breq1
    @58
    @22
    @5
    @24
    @8
    @58
    @21
    cP
    cS
    @58
    @21
    vi
    cD
    @16
    cI
    @15
    cI
    cle
    wbr
    #
    @18
    @15
    cif
    #
    cif
    #
    cmpt
    cP
    @58
    vi
    cD
    @20
    @61
    @58
    @16
    @13
    cI
    @19
    @60
    @58
    id
    @58
    @17
    @59
    @18
    @15
    @13
    cI
    @15
    cle
    breq2
    ifbid
    ifeq12d
    mpteq2dv
    psgnfzto1st.p
    syl6eqr
    fveq2d
    @58
    @23
    @7
    @6
    cexp
    @13
    cI
    c1
    caddc
    oveq1
    oveq2d
    eqeq12d
    imbi12d
    @34
    @1
    @26
    cid
    cD
    cres
    #
    cS
    cfv
    #
    c1
    @31
    @33
    cD
    cfn
    wcel
    #
    @63
    c1
    wceq
    cD
    @11
    cfn
    psgnfzto1st.d
    c1
    cN
    fzfi
    eqeltri
    #
    cD
    cS
    psgnfzto1st.s
    psgnid
    ax-mp
    @30
    @62
    cS
    c1
    c1
    wceq
    @30
    @62
    wceq
    c1
    eqid
    cD
    @30
    vi
    c1
    cN
    psgnfzto1st.d
    @30
    eqid
    fzto1st1
    ax-mp
    fveq2i
    @33
    @6
    c2
    cexp
    co
    c1
    @32
    c2
    @6
    cexp
    1p1e2
    oveq2i
    neg1sqe1
    eqtri
    3eqtr4i
    2a1i
    @1
    @35
    cn
    wcel
    #
    wa
    #
    @45
    wa
    #
    @46
    @54
    @68
    @46
    wa
    #
    @51
    @35
    @42
    cpr
    cD
    cpmtr
    cfv
    #
    cfv
    #
    @40
    ccom
    #
    cS
    cfv
    #
    @71
    cS
    cfv
    #
    @41
    cmul
    co
    #
    @53
    @69
    @50
    @72
    cS
    @67
    @46
    @50
    @72
    wceq
    #
    @45
    @67
    @46
    wa
    #
    @66
    @42
    cD
    wcel
    #
    @76
    @1
    @66
    @46
    simplr
    #
    @77
    @42
    @11
    cD
    @77
    @42
    cn
    wcel
    #
    @1
    @46
    w3a
    @42
    @11
    wcel
    @77
    @80
    @1
    @46
    @77
    @35
    @79
    peano2nnd
    @1
    @66
    @46
    simpll
    #
    @67
    @46
    simpr
    #
    3jca
    cN
    @42
    elfz1b
    sylibr
    psgnfzto1st.d
    syl6eleqr
    #
    cD
    vi
    @35
    cN
    psgnfzto1st.d
    psgnfzto1stlem
    syl2anc
    adantlr
    fveq2d
    @69
    @64
    @71
    cB
    wcel
    @40
    cB
    wcel
    #
    @73
    @75
    wceq
    @64
    @69
    @65
    a1i
    @69
    @70
    crn
    #
    cB
    @71
    cB
    cD
    @85
    cG
    @85
    eqid
    #
    psgnfzto1st.g
    psgnfzto1st.b
    symgtrf
    @67
    @46
    @71
    @85
    wcel
    #
    @45
    @77
    @66
    @78
    @87
    @79
    @83
    cD
    @70
    @35
    cN
    psgnfzto1st.d
    @70
    eqid
    pmtrto1cl
    syl2anc
    #
    adantlr
    sseldi
    @69
    @35
    cD
    wcel
    #
    @84
    @67
    @46
    @89
    @45
    @77
    @35
    @11
    cD
    @77
    @66
    @1
    @36
    w3a
    @35
    @11
    wcel
    @77
    @66
    @1
    @36
    @79
    @81
    @77
    @35
    @42
    cN
    @77
    @35
    @79
    nnred
    #
    @77
    @35
    c1
    @90
    @77
    1red
    readdcld
    @77
    cN
    @81
    nnred
    @77
    @35
    @90
    lep1d
    @82
    letrd
    #
    3jca
    cN
    @35
    elfz1b
    sylibr
    psgnfzto1st.d
    syl6eleqr
    adantlr
    cB
    cD
    @40
    vi
    cG
    @35
    cN
    psgnfzto1st.d
    @40
    eqid
    psgnfzto1st.g
    psgnfzto1st.b
    fzto1st
    syl
    cD
    cB
    cG
    @71
    @40
    cS
    psgnfzto1st.g
    psgnfzto1st.s
    psgnfzto1st.b
    psgnco
    syl3anc
    @69
    @75
    @6
    @43
    cmul
    co
    #
    @53
    @69
    @74
    @6
    @41
    @43
    cmul
    @67
    @46
    @74
    @6
    wceq
    #
    @45
    @77
    @87
    @93
    @88
    cD
    @71
    @85
    cG
    cS
    psgnfzto1st.g
    @86
    psgnfzto1st.s
    psgnpmtr
    syl
    adantlr
    @69
    @36
    @44
    @67
    @46
    @36
    @45
    @91
    adantlr
    @67
    @45
    @46
    simplr
    mpd
    oveq12d
    @66
    @92
    @53
    wceq
    @1
    @45
    @46
    @66
    @53
    @43
    @6
    cmul
    co
    #
    @92
    @66
    @6
    cc
    wcel
    #
    @42
    cn0
    wcel
    @53
    @94
    wceq
    neg1cn
    @66
    @42
    @35
    peano2nn
    nnnn0d
    #
    @6
    @42
    expp1
    sylancr
    @66
    @43
    @6
    @66
    @6
    @42
    @95
    @66
    neg1cn
    a1i
    #
    @96
    expcld
    @97
    mulcomd
    eqtr2d
    ad3antlr
    eqtrd
    3eqtrd
    ex
    nnindd
    imp
    sylbi
    syl
end
