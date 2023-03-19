include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "cmul.mm"
include "cdiv.mm"
include "csqrt.mm"
include "caddc.mm"
include "wceq.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "cr.mm"
include "axsegconlem4.mm"
include "3adant3.mm"
include "ad2antrr.mm"
include "simpl2.mm"
include "fveere.mm"
include "sylan.mm"
include "remulcld.mm"
include "recnd.mm"
include "readdcl.mm"
include "syl2an.mm"
include "adantr.mm"
include "ad2antlr.mm"
include "simpl1.mm"
include "resubcld.mm"
include "cc0.mm"
include "axsegconlem6.mm"
include "gt0ne0d.mm"
include "divsubdird.mm"
include "subsubd.mm"
include "cneg.mm"
include "renegcld.mm"
include "adddid.mm"
include "addcomd.mm"
include "negsubd.mm"
include "eqtrd.mm"
include "negsubdi2d.mm"
include "pncan2d.mm"
include "negeqd.mm"
include "eqtr3d.mm"
include "subdird.mm"
include "cc.mm"
include "mulneg12.mm"
include "syl2anc.mm"
include "3eqtr3rd.mm"
include "divcan3d.mm"
include "sqdivd.mm"
include "sqmuld.mm"
include "cle.mm"
include "wbr.mm"
include "axsegconlem2.mm"
include "axsegconlem3.mm"
include "resqrtth.mm"
include "3eqtrd.mm"
include "sumeq2dv.mm"
include "fzfid.mm"
include "resqcld.mm"
include "fsummulc2.mm"
include "cbvsumv.mm"
include "eqtri.mm"
include "eqtr4i.mm"
include "oveq12i.mm"
include "eqid.mm"
include "wb.mm"
include "sqrt00.mm"
include "necon3bid.mm"
include "mpbid.mm"
include "divmul3d.mm"
include "mpbiri.mm"
include "fsumdivc.mm"

theorem axsegconlem9
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let vi: setvar i
  let vk: setvar k
  let cF: class F
  let cN: class N
  let vp: setvar p
  assume axsegconlem2.1: |- S = sum_ p e. ( 1 ... N ) ( ( ( A ` p ) - ( B ` p ) ) ^ 2 )
  assume axsegconlem7.2: |- T = sum_ p e. ( 1 ... N ) ( ( ( C ` p ) - ( D ` p ) ) ^ 2 )
  assume axsegconlem8.3: |- F = ( k e. ( 1 ... N ) |-> ( ( ( ( ( sqrt ` S ) + ( sqrt ` T ) ) x. ( B ` k ) ) - ( ( sqrt ` T ) x. ( A ` k ) ) ) / ( sqrt ` S ) ) )

  disjoint A i
  disjoint A k
  disjoint i k
  disjoint B i
  disjoint B k
  disjoint C i
  disjoint C k
  disjoint D i
  disjoint D k
  disjoint N i
  disjoint N k
  disjoint S i
  disjoint S k
  disjoint T i
  disjoint T k
  disjoint i p
  disjoint A p
  disjoint B p
  disjoint C p
  disjoint D p
  disjoint N p
  assert |- ( ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ A =/= B ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> sum_ i e. ( 1 ... N ) ( ( ( B ` i ) - ( F ` i ) ) ^ 2 ) = sum_ i e. ( 1 ... N ) ( ( ( C ` i ) - ( D ` i ) ) ^ 2 ) )

  proof
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    cC
    @0
    wcel
    cD
    @0
    wcel
    wa
    #
    wa
    #
    c1
    cN
    cfz
    co
    #
    vi
    cv
    #
    cB
    cfv
    #
    @8
    cF
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    @7
    cT
    @8
    cA
    cfv
    #
    @9
    cmin
    co
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    cS
    cdiv
    co
    #
    vi
    csu
    #
    @7
    @8
    cC
    cfv
    #
    @8
    cD
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    @6
    @7
    @12
    @17
    vi
    @6
    @8
    @7
    wcel
    #
    wa
    #
    @12
    cT
    csqrt
    cfv
    #
    @14
    cmul
    co
    #
    cS
    csqrt
    cfv
    #
    cdiv
    co
    #
    c2
    cexp
    co
    @27
    c2
    cexp
    co
    #
    @28
    c2
    cexp
    co
    #
    cdiv
    co
    @17
    @25
    @11
    @29
    c2
    cexp
    @25
    @11
    @9
    @28
    @26
    caddc
    co
    #
    @9
    cmul
    co
    #
    @26
    @13
    cmul
    co
    #
    cmin
    co
    #
    @28
    cdiv
    co
    #
    cmin
    co
    #
    @29
    @25
    @10
    @36
    @9
    cmin
    @24
    @10
    @36
    wceq
    @6
    vk
    @8
    @32
    vk
    cv
    #
    cB
    cfv
    #
    cmul
    co
    #
    @26
    @38
    cA
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @28
    cdiv
    co
    @36
    @7
    cF
    vk
    vi
    weq
    #
    @43
    @35
    @28
    cdiv
    @44
    @40
    @33
    @42
    @34
    cmin
    @44
    @39
    @9
    @32
    cmul
    @38
    @8
    cB
    fveq2
    oveq2d
    @44
    @41
    @13
    @26
    cmul
    @38
    @8
    cA
    fveq2
    oveq2d
    oveq12d
    oveq1d
    axsegconlem8.3
    @35
    @28
    cdiv
    ovex
    fvmpt
    adantl
    oveq2d
    @25
    @28
    @9
    cmul
    co
    #
    @35
    cmin
    co
    #
    @28
    cdiv
    co
    @45
    @28
    cdiv
    co
    #
    @36
    cmin
    co
    @29
    @37
    @25
    @45
    @35
    @28
    @25
    @45
    @25
    @28
    @9
    @4
    @28
    cr
    wcel
    #
    @5
    @24
    @1
    @2
    @48
    @3
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem4
    3adant3
    #
    ad2antrr
    #
    @6
    @2
    @24
    @9
    cr
    wcel
    @1
    @2
    @3
    @5
    simpl2
    cB
    @8
    cN
    fveere
    sylan
    #
    remulcld
    recnd
    #
    @25
    @35
    @25
    @33
    @34
    @25
    @32
    @9
    @6
    @32
    cr
    wcel
    #
    @24
    @4
    @48
    @26
    cr
    wcel
    #
    @53
    @5
    @49
    cC
    cD
    cT
    cN
    vp
    axsegconlem7.2
    axsegconlem4
    #
    @28
    @26
    readdcl
    syl2an
    adantr
    #
    @51
    remulcld
    #
    @25
    @26
    @13
    @5
    @54
    @4
    @24
    @55
    ad2antlr
    #
    @6
    @1
    @24
    @13
    cr
    wcel
    @1
    @2
    @3
    @5
    simpl1
    cA
    @8
    cN
    fveere
    sylan
    #
    remulcld
    #
    resubcld
    recnd
    @25
    @28
    @50
    recnd
    #
    @4
    @28
    cc0
    wne
    #
    @5
    @24
    @4
    @28
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem6
    gt0ne0d
    #
    ad2antrr
    #
    divsubdird
    @25
    @46
    @27
    @28
    cdiv
    @25
    @46
    @45
    @33
    cmin
    co
    #
    @34
    caddc
    co
    #
    @27
    @25
    @45
    @33
    @34
    @52
    @25
    @33
    @57
    recnd
    @25
    @34
    @60
    recnd
    subsubd
    @25
    @26
    @9
    cneg
    #
    @13
    caddc
    co
    #
    cmul
    co
    @26
    @67
    cmul
    co
    #
    @34
    caddc
    co
    @27
    @66
    @25
    @26
    @67
    @13
    @25
    @26
    @58
    recnd
    #
    @25
    @67
    @25
    @9
    @51
    renegcld
    recnd
    #
    @25
    @13
    @59
    recnd
    #
    adddid
    @25
    @68
    @14
    @26
    cmul
    @25
    @68
    @13
    @67
    caddc
    co
    @14
    @25
    @67
    @13
    @71
    @72
    addcomd
    @25
    @13
    @9
    @72
    @25
    @9
    @51
    recnd
    #
    negsubd
    eqtrd
    oveq2d
    @25
    @69
    @65
    @34
    caddc
    @25
    @28
    @32
    cmin
    co
    #
    @9
    cmul
    co
    @26
    cneg
    #
    @9
    cmul
    co
    #
    @65
    @69
    @25
    @74
    @75
    @9
    cmul
    @25
    @32
    @28
    cmin
    co
    #
    cneg
    @74
    @75
    @25
    @32
    @28
    @25
    @32
    @56
    recnd
    #
    @61
    negsubdi2d
    @25
    @77
    @26
    @25
    @28
    @26
    @61
    @70
    pncan2d
    negeqd
    eqtr3d
    oveq1d
    @25
    @28
    @32
    @9
    @61
    @78
    @73
    subdird
    @25
    @26
    cc
    wcel
    @9
    cc
    wcel
    @76
    @69
    wceq
    @70
    @73
    @26
    @9
    mulneg12
    syl2anc
    3eqtr3rd
    oveq1d
    3eqtr3rd
    eqtrd
    oveq1d
    @25
    @47
    @9
    @36
    cmin
    @25
    @9
    @28
    @73
    @61
    @64
    divcan3d
    oveq1d
    3eqtr3rd
    eqtrd
    oveq1d
    @25
    @27
    @28
    @25
    @27
    @25
    @26
    @14
    @58
    @25
    @13
    @9
    @59
    @51
    resubcld
    #
    remulcld
    recnd
    @61
    @64
    sqdivd
    @25
    @30
    @16
    @31
    cS
    cdiv
    @25
    @30
    @26
    c2
    cexp
    co
    #
    @15
    cmul
    co
    @16
    @25
    @26
    @14
    @70
    @25
    @14
    @79
    recnd
    sqmuld
    @25
    @80
    cT
    @15
    cmul
    @25
    cT
    cr
    wcel
    #
    cc0
    cT
    cle
    wbr
    #
    @80
    cT
    wceq
    @5
    @81
    @4
    @24
    cC
    cD
    cT
    cN
    vp
    axsegconlem7.2
    axsegconlem2
    #
    ad2antlr
    #
    @5
    @82
    @4
    @24
    cC
    cD
    cT
    cN
    vp
    axsegconlem7.2
    axsegconlem3
    ad2antlr
    cT
    resqrtth
    syl2anc
    oveq1d
    eqtrd
    @4
    @31
    cS
    wceq
    #
    @5
    @24
    @1
    @2
    @85
    @3
    @1
    @2
    wa
    cS
    cr
    wcel
    #
    cc0
    cS
    cle
    wbr
    #
    @85
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem2
    #
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem3
    #
    cS
    resqrtth
    syl2anc
    3adant3
    ad2antrr
    oveq12d
    3eqtrd
    sumeq2dv
    @6
    cT
    @7
    @15
    vi
    csu
    #
    cmul
    co
    #
    cS
    cdiv
    co
    #
    @7
    @16
    vi
    csu
    #
    cS
    cdiv
    co
    @23
    @18
    @6
    @91
    @93
    cS
    cdiv
    @6
    @7
    @15
    cT
    vi
    @6
    c1
    cN
    fzfid
    #
    @6
    cT
    @5
    @81
    @4
    @83
    adantl
    #
    recnd
    @25
    @15
    @25
    @14
    @79
    resqcld
    #
    recnd
    fsummulc2
    oveq1d
    @6
    @92
    @23
    wceq
    @91
    @23
    cS
    cmul
    co
    wceq
    cT
    @23
    @90
    cS
    cmul
    cT
    @7
    vp
    cv
    #
    cC
    cfv
    #
    @97
    cD
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vp
    csu
    @23
    axsegconlem7.2
    @7
    @101
    @22
    vp
    vi
    vp
    vi
    weq
    #
    @100
    @21
    c2
    cexp
    @102
    @98
    @19
    @99
    @20
    cmin
    @97
    @8
    cC
    fveq2
    @97
    @8
    cD
    fveq2
    oveq12d
    oveq1d
    cbvsumv
    eqtri
    @90
    @7
    @97
    cA
    cfv
    #
    @97
    cB
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vp
    csu
    cS
    @7
    @15
    @106
    vi
    vp
    vi
    vp
    weq
    #
    @14
    @105
    c2
    cexp
    @107
    @13
    @103
    @9
    @104
    cmin
    @8
    @97
    cA
    fveq2
    @8
    @97
    cB
    fveq2
    oveq12d
    oveq1d
    cbvsumv
    axsegconlem2.1
    eqtr4i
    oveq12i
    @6
    @91
    @23
    cS
    @6
    @91
    @6
    cT
    @90
    @95
    @4
    @90
    cr
    wcel
    #
    @5
    @1
    @2
    @108
    @3
    cA
    cB
    @90
    cN
    vi
    @90
    eqid
    axsegconlem2
    3adant3
    adantr
    remulcld
    recnd
    @6
    @23
    @5
    @23
    cr
    wcel
    @4
    cC
    cD
    @23
    cN
    vi
    @23
    eqid
    axsegconlem2
    adantl
    recnd
    @6
    cS
    @4
    @86
    @5
    @1
    @2
    @86
    @3
    @88
    3adant3
    #
    adantr
    recnd
    #
    @4
    cS
    cc0
    wne
    #
    @5
    @4
    @62
    @111
    @63
    @4
    @86
    @87
    @62
    @111
    wb
    @109
    @1
    @2
    @87
    @3
    @89
    3adant3
    @86
    @87
    wa
    @28
    cc0
    cS
    cc0
    cS
    sqrt00
    necon3bid
    syl2anc
    mpbid
    adantr
    #
    divmul3d
    mpbiri
    @6
    @7
    @16
    cS
    vi
    @94
    @110
    @25
    @16
    @25
    cT
    @15
    @84
    @96
    remulcld
    recnd
    @112
    fsumdivc
    3eqtr3rd
    eqtrd
end
