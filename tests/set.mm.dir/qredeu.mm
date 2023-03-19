include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "cz.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cgcd.mm"
include "c1.mm"
include "wa.mm"
include "cxp.mm"
include "wi.mm"
include "wral.mm"
include "cq.mm"
include "wcel.mm"
include "wreu.mm"
include "w3a.mm"
include "cop.mm"
include "cdvds.mm"
include "wbr.mm"
include "nnz.mm"
include "gcddvds.mm"
include "simpld.mm"
include "sylan2.mm"
include "cc0.mm"
include "wne.mm"
include "wb.mm"
include "cn0.mm"
include "gcdcl.mm"
include "nn0zd.mm"
include "wn.mm"
include "simpl.mm"
include "adantl.mm"
include "nnne0.mm"
include "neneqd.mm"
include "intnand.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "syl.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "3adant3.mm"
include "clt.mm"
include "simprd.mm"
include "cr.mm"
include "nnre.mm"
include "nn0red.mm"
include "nngt0.mm"
include "divgt0d.mm"
include "jca.mm"
include "elnnz.mm"
include "sylibr.mm"
include "opelxpd.mm"
include "gcdcld.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "cmul.mm"
include "mulid1d.mm"
include "cc.mm"
include "zcn.mm"
include "adantr.mm"
include "divcan2d.mm"
include "nncn.mm"
include "oveq12d.mm"
include "mulgcd.mm"
include "3eqtr2rd.mm"
include "mulcanad.mm"
include "divcan7d.mm"
include "eqeq2d.mm"
include "biimp3ar.mm"
include "ovex.mm"
include "op1std.mm"
include "op2ndd.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "elxp6.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "simprll.mm"
include "ad2antlr.mm"
include "simprrl.mm"
include "simprlr.mm"
include "simprrr.mm"
include "eqtr3d.mm"
include "qredeq.mm"
include "syl331anc.mm"
include "fvex.mm"
include "opth.mm"
include "simplll.mm"
include "simplrl.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "syl2anb.mm"
include "rgen2a.mm"
include "jctir.mm"
include "3expia.mm"
include "rexlimivv.mm"
include "elq.mm"
include "fveq2.mm"
include "reu4.mm"
include "3imtr4i.mm"

theorem qredeu
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( A e. QQ -> E! x e. ( ZZ X. NN ) ( ( ( 1st ` x ) gcd ( 2nd ` x ) ) = 1 /\ A = ( ( 1st ` x ) / ( 2nd ` x ) ) ) )

  proof
    cA
    vz
    cv
    #
    vn
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vn
    cn
    wrex
    vz
    cz
    wrex
    vx
    cv
    #
    c1st
    cfv
    #
    @4
    c2nd
    cfv
    #
    cgcd
    co
    #
    c1
    wceq
    #
    cA
    @5
    @6
    cdiv
    co
    #
    wceq
    #
    wa
    #
    vx
    cz
    cn
    cxp
    #
    wrex
    #
    @11
    vy
    cv
    #
    c1st
    cfv
    #
    @14
    c2nd
    cfv
    #
    cgcd
    co
    #
    c1
    wceq
    #
    cA
    @15
    @16
    cdiv
    co
    #
    wceq
    #
    wa
    #
    wa
    #
    @4
    @14
    wceq
    #
    wi
    #
    vy
    @12
    wral
    vx
    @12
    wral
    #
    wa
    #
    cA
    cq
    wcel
    @11
    vx
    @12
    wreu
    @3
    @26
    vz
    vn
    cz
    cn
    @0
    cz
    wcel
    #
    @1
    cn
    wcel
    #
    @3
    @26
    @27
    @28
    @3
    w3a
    #
    @13
    @25
    @29
    @0
    @0
    @1
    cgcd
    co
    #
    cdiv
    co
    #
    @1
    @30
    cdiv
    co
    #
    cop
    #
    @12
    wcel
    @31
    @32
    cgcd
    co
    #
    c1
    wceq
    #
    cA
    @31
    @32
    cdiv
    co
    #
    wceq
    #
    @13
    @29
    @31
    @32
    cz
    cn
    @27
    @28
    @31
    cz
    wcel
    #
    @3
    @27
    @28
    wa
    #
    @30
    @0
    cdvds
    wbr
    #
    @38
    @28
    @27
    @1
    cz
    wcel
    #
    @40
    @1
    nnz
    #
    @27
    @41
    wa
    #
    @40
    @30
    @1
    cdvds
    wbr
    #
    @0
    @1
    gcddvds
    #
    simpld
    sylan2
    @39
    @30
    cz
    wcel
    #
    @30
    cc0
    wne
    #
    @27
    @40
    @38
    wb
    @39
    @30
    @28
    @27
    @41
    @30
    cn0
    wcel
    #
    @42
    @0
    @1
    gcdcl
    sylan2
    #
    nn0zd
    #
    @39
    @30
    cn
    wcel
    #
    @47
    @39
    @27
    @41
    @0
    cc0
    wceq
    #
    @1
    cc0
    wceq
    #
    wa
    wn
    #
    @51
    @27
    @28
    simpl
    #
    @28
    @41
    @27
    @42
    adantl
    #
    @28
    @54
    @27
    @28
    @53
    @52
    @28
    @1
    cc0
    @1
    nnne0
    #
    neneqd
    intnand
    adantl
    @0
    @1
    gcdn0cl
    syl21anc
    #
    @30
    nnne0
    syl
    #
    @55
    @30
    @0
    dvdsval2
    syl3anc
    mpbid
    #
    3adant3
    @29
    @32
    cz
    wcel
    #
    cc0
    @32
    clt
    wbr
    #
    wa
    #
    @32
    cn
    wcel
    @27
    @28
    @63
    @3
    @39
    @61
    @62
    @39
    @44
    @61
    @28
    @27
    @41
    @44
    @42
    @43
    @40
    @44
    @45
    simprd
    sylan2
    @39
    @46
    @47
    @41
    @44
    @61
    wb
    @50
    @59
    @56
    @30
    @1
    dvdsval2
    syl3anc
    mpbid
    #
    @39
    @1
    @30
    @28
    @1
    cr
    wcel
    @27
    @1
    nnre
    adantl
    @39
    @30
    @49
    nn0red
    @28
    cc0
    @1
    clt
    wbr
    @27
    @1
    nngt0
    adantl
    @39
    @51
    cc0
    @30
    clt
    wbr
    @58
    @30
    nngt0
    syl
    divgt0d
    jca
    3adant3
    @32
    elnnz
    sylibr
    opelxpd
    @27
    @28
    @35
    @3
    @39
    @34
    c1
    @30
    @39
    @34
    @39
    @31
    @32
    @60
    @64
    gcdcld
    nn0cnd
    @39
    1cnd
    @39
    @30
    @49
    nn0cnd
    #
    @59
    @39
    @30
    c1
    cmul
    co
    @30
    @30
    @31
    cmul
    co
    #
    @30
    @32
    cmul
    co
    #
    cgcd
    co
    #
    @30
    @34
    cmul
    co
    #
    @39
    @30
    @65
    mulid1d
    @39
    @66
    @0
    @67
    @1
    cgcd
    @39
    @0
    @30
    @27
    @0
    cc
    wcel
    @28
    @0
    zcn
    adantr
    #
    @65
    @59
    divcan2d
    @39
    @1
    @30
    @28
    @1
    cc
    wcel
    @27
    @1
    nncn
    adantl
    #
    @65
    @59
    divcan2d
    oveq12d
    @39
    @48
    @38
    @61
    @68
    @69
    wceq
    @49
    @60
    @64
    @30
    @31
    @32
    mulgcd
    syl3anc
    3eqtr2rd
    mulcanad
    3adant3
    @27
    @28
    @37
    @3
    @39
    @36
    @2
    cA
    @39
    @0
    @1
    @30
    @70
    @71
    @65
    @28
    @1
    cc0
    wne
    @27
    @57
    adantl
    @59
    divcan7d
    eqeq2d
    biimp3ar
    @11
    @35
    @37
    wa
    vx
    @33
    @12
    @4
    @33
    wceq
    #
    @8
    @35
    @10
    @37
    @72
    @7
    @34
    c1
    @72
    @5
    @31
    @6
    @32
    cgcd
    @31
    @32
    @4
    @0
    @30
    cdiv
    ovex
    #
    @1
    @30
    cdiv
    ovex
    #
    op1std
    #
    @31
    @32
    @4
    @73
    @74
    op2ndd
    #
    oveq12d
    eqeq1d
    @72
    @9
    @36
    cA
    @72
    @5
    @31
    @6
    @32
    cdiv
    @75
    @76
    oveq12d
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    @24
    vx
    vy
    @12
    @4
    @12
    wcel
    @4
    @5
    @6
    cop
    #
    wceq
    #
    @5
    cz
    wcel
    #
    @6
    cn
    wcel
    #
    wa
    #
    wa
    #
    @14
    @15
    @16
    cop
    #
    wceq
    #
    @15
    cz
    wcel
    #
    @16
    cn
    wcel
    #
    wa
    #
    wa
    #
    @24
    @14
    @12
    wcel
    @4
    cz
    cn
    elxp6
    @14
    cz
    cn
    elxp6
    @82
    @88
    wa
    #
    @22
    @23
    @89
    @22
    wa
    #
    @77
    @83
    @4
    @14
    @90
    @5
    @15
    wceq
    @6
    @16
    wceq
    wa
    #
    @77
    @83
    wceq
    @90
    @79
    @80
    @8
    @85
    @86
    @18
    @9
    @19
    wceq
    @91
    @82
    @79
    @88
    @22
    @78
    @79
    @80
    simprl
    ad2antrr
    @82
    @80
    @88
    @22
    @78
    @79
    @80
    simprr
    ad2antrr
    @89
    @8
    @10
    @21
    simprll
    @88
    @85
    @82
    @22
    @84
    @85
    @86
    simprl
    ad2antlr
    @88
    @86
    @82
    @22
    @84
    @85
    @86
    simprr
    ad2antlr
    @89
    @11
    @18
    @20
    simprrl
    @90
    cA
    @9
    @19
    @89
    @8
    @10
    @21
    simprlr
    @89
    @11
    @18
    @20
    simprrr
    eqtr3d
    @15
    @16
    @5
    @6
    qredeq
    syl331anc
    @5
    @6
    @15
    @16
    @4
    c1st
    fvex
    @4
    c2nd
    fvex
    opth
    sylibr
    @78
    @81
    @88
    @22
    simplll
    @82
    @84
    @87
    @22
    simplrl
    3eqtr4d
    ex
    syl2anb
    rgen2a
    jctir
    3expia
    rexlimivv
    vz
    vn
    cA
    elq
    @11
    @21
    vx
    vy
    @12
    @23
    @8
    @18
    @10
    @20
    @23
    @7
    @17
    c1
    @23
    @5
    @15
    @6
    @16
    cgcd
    @4
    @14
    c1st
    fveq2
    #
    @4
    @14
    c2nd
    fveq2
    #
    oveq12d
    eqeq1d
    @23
    @9
    @19
    cA
    @23
    @5
    @15
    @6
    @16
    cdiv
    @92
    @93
    oveq12d
    eqeq2d
    anbi12d
    reu4
    3imtr4i
end
