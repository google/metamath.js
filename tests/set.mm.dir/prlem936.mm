include "cnq.mm"
include "wcel.mm"
include "cnp.mm"
include "c1q.mm"
include "cltq.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cmq.mm"
include "co.mm"
include "wn.mm"
include "wrex.mm"
include "ltrelnq.mm"
include "brel.mm"
include "simprd.mm"
include "adantl.mm"
include "wi.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "notbid.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "prn0.mm"
include "n0.mm"
include "sylib.mm"
include "adantr.mm"
include "cplq.mm"
include "elprnq.mm"
include "ad2ant2r.mm"
include "mulidnq.mm"
include "syl.mm"
include "simplr.mm"
include "ltmnq.mm"
include "biimpa.mm"
include "syl2anc.mm"
include "eqbrtrrd.mm"
include "wb.mm"
include "ad2antlr.mm"
include "mulclnq.mm"
include "ltexnq.mm"
include "mpbid.mm"
include "simplll.mm"
include "vex.mm"
include "prlem934.mm"
include "simprr.mm"
include "eleq1.mm"
include "biimparc.mm"
include "sylan.mm"
include "cxp.mm"
include "addnqf.mm"
include "fdmi.mm"
include "0nnq.mm"
include "ndmovrcl.mm"
include "addclnq.mm"
include "prub.mm"
include "syl21anc.mm"
include "ad2antrr.mm"
include "crq.mm"
include "cfv.mm"
include "recclnq.mm"
include "sylan2.mm"
include "ancoms.mm"
include "mulassnq.mm"
include "mulcomnq.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "recidnq.mm"
include "oveq2d.mm"
include "sylan9eq.mm"
include "syl5eq.mm"
include "breq1d.mm"
include "bitrd.mm"
include "adantll.mm"
include "mulnqf.mm"
include "simpld.mm"
include "ltanq.mm"
include "ovex.mm"
include "distrnq.mm"
include "caovdir.mm"
include "fvex.mm"
include "caov12.mm"
include "sylan9eqr.mm"
include "eqtr4i.mm"
include "a1i.mm"
include "oveq12d.mm"
include "breq2d.mm"
include "bitr4d.mm"
include "adantrr.mm"
include "addcomnq.mm"
include "breq12i.mm"
include "syl6bb.mm"
include "ad2antrl.mm"
include "oveq1.mm"
include "caov411.mm"
include "adantrl.mm"
include "3bitr3d.mm"
include "syl22anc.mm"
include "sylibd.mm"
include "prcdnq.mm"
include "impancom.mm"
include "con3d.mm"
include "ex.mm"
include "com23.mm"
include "mpdd.mm"
include "reximdva.mm"
include "mpd.mm"
include "exlimddv.mm"
include "expr.mm"
include "rspcev.mm"
include "pm2.61d.mm"
include "vtoclg.mm"
include "mpcom.mm"

theorem prlem936
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint b x
  disjoint y z
  disjoint b y
  disjoint A y
  disjoint b z
  disjoint A z
  disjoint A b
  disjoint B b
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- ( ( A e. P. /\ 1Q <Q B ) -> E. x e. A -. ( x .Q B ) e. A )

  proof
    cB
    cnq
    wcel
    #
    cA
    cnp
    wcel
    #
    c1q
    cB
    cltq
    wbr
    #
    wa
    #
    vx
    cv
    #
    cB
    cmq
    co
    #
    cA
    wcel
    #
    wn
    #
    vx
    cA
    wrex
    #
    @2
    @0
    @1
    @2
    c1q
    cnq
    wcel
    #
    @0
    c1q
    cB
    cnq
    cnq
    cltq
    ltrelnq
    brel
    simprd
    adantl
    @1
    c1q
    vb
    cv
    #
    cltq
    wbr
    #
    wa
    #
    @4
    @10
    cmq
    co
    #
    cA
    wcel
    #
    wn
    #
    vx
    cA
    wrex
    #
    wi
    @3
    @8
    wi
    vb
    cB
    cnq
    @10
    cB
    wceq
    #
    @12
    @3
    @16
    @8
    @17
    @11
    @2
    @1
    @10
    cB
    c1q
    cltq
    breq2
    anbi2d
    @17
    @15
    @7
    vx
    cA
    @17
    @14
    @6
    @17
    @13
    @5
    cA
    @10
    cB
    @4
    cmq
    oveq2
    eleq1d
    notbid
    rexbidv
    imbi12d
    @12
    vy
    cv
    #
    cA
    wcel
    #
    @16
    vy
    @1
    @19
    vy
    wex
    #
    @11
    @1
    cA
    c0
    wne
    @20
    cA
    prn0
    vy
    cA
    n0
    sylib
    adantr
    @12
    @19
    wa
    @18
    @10
    cmq
    co
    #
    cA
    wcel
    #
    @16
    @12
    @19
    @22
    @16
    @12
    @19
    @22
    wa
    #
    wa
    #
    @18
    vz
    cv
    #
    cplq
    co
    #
    @21
    wceq
    #
    @16
    vz
    @24
    @18
    @21
    cltq
    wbr
    #
    @27
    vz
    wex
    #
    @24
    @18
    c1q
    cmq
    co
    #
    @18
    @21
    cltq
    @24
    @18
    cnq
    wcel
    #
    @30
    @18
    wceq
    @1
    @19
    @31
    @11
    @22
    cA
    @18
    elprnq
    ad2ant2r
    #
    @18
    mulidnq
    syl
    @24
    @31
    @11
    @30
    @21
    cltq
    wbr
    #
    @32
    @1
    @11
    @23
    simplr
    @31
    @11
    @33
    c1q
    @10
    @18
    ltmnq
    biimpa
    syl2anc
    eqbrtrrd
    @24
    @21
    cnq
    wcel
    #
    @28
    @29
    wb
    @24
    @31
    @10
    cnq
    wcel
    #
    @34
    @32
    @11
    @35
    @1
    @23
    @11
    @9
    @35
    c1q
    @10
    cnq
    cnq
    cltq
    ltrelnq
    brel
    simprd
    ad2antlr
    #
    @18
    @10
    mulclnq
    syl2anc
    vz
    @18
    @21
    ltexnq
    syl
    mpbid
    @24
    @27
    wa
    #
    @4
    @25
    cplq
    co
    #
    cA
    wcel
    #
    wn
    #
    vx
    cA
    wrex
    #
    @16
    @37
    @1
    @41
    @1
    @11
    @23
    @27
    simplll
    #
    vx
    cA
    @25
    vz
    vex
    #
    prlem934
    syl
    @37
    @40
    @15
    vx
    cA
    @37
    @4
    cA
    wcel
    #
    wa
    #
    @40
    @38
    @13
    cltq
    wbr
    #
    @15
    @45
    @40
    @26
    @38
    cltq
    wbr
    #
    @46
    @45
    @1
    @26
    cA
    wcel
    #
    @38
    cnq
    wcel
    #
    @40
    @47
    wi
    @37
    @1
    @44
    @42
    adantr
    #
    @37
    @48
    @44
    @24
    @22
    @27
    @48
    @12
    @19
    @22
    simprr
    @27
    @48
    @22
    @26
    @21
    cA
    eleq1
    biimparc
    sylan
    #
    adantr
    @45
    @4
    cnq
    wcel
    #
    @25
    cnq
    wcel
    #
    @49
    @37
    @1
    @44
    @52
    @42
    cA
    @4
    elprnq
    sylan
    #
    @37
    @53
    @44
    @37
    @1
    @48
    @53
    @42
    @51
    @1
    @48
    wa
    @26
    cnq
    wcel
    #
    @53
    cA
    @26
    elprnq
    @55
    @31
    @53
    @18
    @25
    cnq
    cplq
    cnq
    cnq
    cxp
    #
    cnq
    cplq
    addnqf
    fdmi
    0nnq
    ndmovrcl
    simprd
    syl
    syl2anc
    adantr
    #
    @4
    @25
    addclnq
    syl2anc
    cA
    @26
    @38
    prub
    syl21anc
    @45
    @13
    cnq
    wcel
    #
    @31
    @53
    @27
    @47
    @46
    wb
    @45
    @52
    @35
    @58
    @54
    @24
    @35
    @27
    @44
    @36
    ad2antrr
    @4
    @10
    mulclnq
    syl2anc
    @24
    @31
    @27
    @44
    @32
    ad2antrr
    @57
    @24
    @27
    @44
    simplr
    @58
    @31
    wa
    #
    @53
    @27
    wa
    wa
    @18
    @4
    cltq
    wbr
    #
    @38
    @26
    @4
    @18
    crq
    cfv
    #
    cmq
    co
    #
    cmq
    co
    #
    cltq
    wbr
    #
    @47
    @46
    @59
    @53
    @60
    @64
    wb
    @27
    @59
    @53
    wa
    @60
    @25
    @25
    @61
    cmq
    co
    #
    @4
    cmq
    co
    #
    cltq
    wbr
    #
    @64
    @31
    @53
    @60
    @67
    wb
    @58
    @31
    @53
    wa
    #
    @60
    @65
    @18
    cmq
    co
    #
    @66
    cltq
    wbr
    #
    @67
    @68
    @65
    cnq
    wcel
    #
    @60
    @70
    wb
    @53
    @31
    @71
    @31
    @53
    @61
    cnq
    wcel
    @71
    @18
    recclnq
    @25
    @61
    mulclnq
    sylan2
    ancoms
    @18
    @4
    @65
    ltmnq
    syl
    @68
    @69
    @25
    @66
    cltq
    @68
    @69
    @25
    @18
    @61
    cmq
    co
    #
    cmq
    co
    #
    @25
    @69
    @25
    @61
    @18
    cmq
    co
    #
    cmq
    co
    @73
    @25
    @61
    @18
    mulassnq
    @74
    @72
    @25
    cmq
    @61
    @18
    mulcomnq
    oveq2i
    eqtri
    @31
    @53
    @73
    @25
    c1q
    cmq
    co
    @25
    @31
    @72
    c1q
    @25
    cmq
    @18
    recidnq
    #
    oveq2d
    @25
    mulidnq
    sylan9eq
    syl5eq
    breq1d
    bitrd
    adantll
    @59
    @67
    @64
    wb
    @53
    @59
    @67
    @38
    @4
    @66
    cplq
    co
    #
    cltq
    wbr
    #
    @64
    @58
    @67
    @77
    wb
    #
    @31
    @58
    @52
    @78
    @58
    @52
    @35
    @4
    @10
    cnq
    cmq
    @56
    cnq
    cmq
    mulnqf
    fdmi
    0nnq
    ndmovrcl
    simpld
    #
    @25
    @66
    @4
    ltanq
    syl
    adantr
    @59
    @63
    @76
    @38
    cltq
    @59
    @63
    @18
    @62
    cmq
    co
    #
    @25
    @62
    cmq
    co
    #
    cplq
    co
    @76
    vu
    vw
    vv
    @18
    @25
    @62
    cplq
    cmq
    vy
    vex
    #
    @43
    @4
    @61
    cmq
    ovex
    vu
    cv
    #
    vw
    cv
    #
    mulcomnq
    #
    @83
    @84
    vv
    cv
    #
    distrnq
    caovdir
    @59
    @80
    @4
    @81
    @66
    cplq
    @59
    @80
    @4
    @72
    cmq
    co
    #
    @4
    vu
    vw
    vv
    @18
    @4
    @61
    cmq
    @82
    vx
    vex
    #
    @18
    crq
    fvex
    #
    @85
    @83
    @84
    @86
    mulassnq
    #
    caov12
    @31
    @58
    @87
    @4
    c1q
    cmq
    co
    #
    @4
    @31
    @72
    c1q
    @4
    cmq
    @75
    oveq2d
    @58
    @52
    @91
    @4
    wceq
    @79
    @4
    mulidnq
    syl
    sylan9eqr
    syl5eq
    @81
    @66
    wceq
    @59
    @81
    @25
    @61
    @4
    cmq
    co
    #
    cmq
    co
    @66
    @62
    @92
    @25
    cmq
    @4
    @61
    mulcomnq
    oveq2i
    @25
    @61
    @4
    mulassnq
    eqtr4i
    a1i
    oveq12d
    syl5eq
    breq2d
    bitr4d
    adantr
    bitrd
    adantrr
    @53
    @60
    @47
    wb
    @59
    @27
    @53
    @60
    @25
    @18
    cplq
    co
    #
    @25
    @4
    cplq
    co
    #
    cltq
    wbr
    @47
    @18
    @4
    @25
    ltanq
    @93
    @26
    @94
    @38
    cltq
    @25
    @18
    addcomnq
    @25
    @4
    addcomnq
    breq12i
    syl6bb
    ad2antrl
    @59
    @27
    @64
    @46
    wb
    @53
    @59
    @27
    wa
    @63
    @13
    @38
    cltq
    @27
    @59
    @63
    @21
    @62
    cmq
    co
    #
    @13
    @26
    @21
    @62
    cmq
    oveq1
    @59
    @95
    @13
    @72
    cmq
    co
    #
    @13
    vu
    vw
    vv
    @18
    @10
    @4
    @61
    cmq
    @82
    vb
    vex
    @88
    @85
    @90
    @89
    caov411
    @31
    @58
    @96
    @13
    c1q
    cmq
    co
    @13
    @31
    @72
    c1q
    @13
    cmq
    @75
    oveq2d
    @13
    mulidnq
    sylan9eqr
    syl5eq
    sylan9eqr
    breq2d
    adantrl
    3bitr3d
    syl22anc
    sylibd
    @45
    @1
    @40
    @46
    @15
    wi
    wi
    @50
    @1
    @46
    @40
    @15
    @1
    @46
    @40
    @15
    wi
    @1
    @46
    wa
    @14
    @39
    @1
    @14
    @46
    @39
    cA
    @13
    @38
    prcdnq
    impancom
    con3d
    ex
    com23
    syl
    mpdd
    reximdva
    mpd
    exlimddv
    expr
    @19
    @22
    wn
    #
    @16
    wi
    @12
    @19
    @97
    @16
    @15
    @97
    vx
    @18
    cA
    @4
    @18
    wceq
    #
    @14
    @22
    @98
    @13
    @21
    cA
    @4
    @18
    @10
    cmq
    oveq1
    eleq1d
    notbid
    rspcev
    ex
    adantl
    pm2.61d
    exlimddv
    vtoclg
    mpcom
end
