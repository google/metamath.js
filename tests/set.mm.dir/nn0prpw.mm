include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "wb.mm"
include "cn.mm"
include "wral.mm"
include "cprime.mm"
include "breq2.mm"
include "a1d.mm"
include "ralrimivv.mm"
include "cc0.mm"
include "wo.mm"
include "wi.mm"
include "elnn0.mm"
include "wne.mm"
include "wn.mm"
include "wrex.mm"
include "clt.mm"
include "cr.mm"
include "nnre.mm"
include "lttri2.mm"
include "syl2an.mm"
include "ancoms.mm"
include "nn0prpwlem.mm"
include "breq1.mm"
include "bibi1d.mm"
include "notbid.mm"
include "2rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "mpan9.mm"
include "bicom.mm"
include "syl6bb.mm"
include "syl5com.mm"
include "impcom.mm"
include "jaod.mm"
include "sylbid.mm"
include "df-ne.mm"
include "rexnal2.mm"
include "3imtr3g.mm"
include "con4d.mm"
include "ex.mm"
include "prmunb.mm"
include "w3a.mm"
include "c1.mm"
include "1nn.mm"
include "cle.mm"
include "cz.mm"
include "prmz.mm"
include "1nn0.mm"
include "zexpcl.mm"
include "sylancl.mm"
include "dvdsle.mm"
include "sylan.mm"
include "prmnn.mm"
include "syl.mm"
include "reexpcl.mm"
include "lenlt.mm"
include "nncnd.mm"
include "exp1d.mm"
include "adantr.mm"
include "breq2d.mm"
include "bitrd.mm"
include "sylibd.mm"
include "con2d.mm"
include "3impia.mm"
include "dvds0.mm"
include "3ad2ant2.mm"
include "idd.mm"
include "mpid.mm"
include "mtod.mm"
include "biimpr.mm"
include "nsyl.mm"
include "oveq2.mm"
include "breq1d.mm"
include "bibi12d.mm"
include "rspcev.mm"
include "sylancr.mm"
include "3expia.mm"
include "reximdva.mm"
include "mpd.mm"
include "sylib.mm"
include "pm2.21d.mm"
include "bibi2d.mm"
include "2ralbidv.mm"
include "eqeq2.mm"
include "syl5ibr.mm"
include "jaoi.mm"
include "sylbi.mm"
include "com12.mm"
include "orcom.mm"
include "df-or.mm"
include "3bitri.mm"
include "biimp.mm"
include "imim2i.mm"
include "eqcom.mm"
include "syl6ib.mm"
include "eqeq1.mm"
include "imp.mm"
include "sylanb.mm"
include "impbid2.mm"

theorem nn0prpw
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vp: setvar p
  let vk: setvar k
  let vm: setvar m
  let vq: setvar q
  let vr: setvar r
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y

  disjoint n p
  disjoint A n
  disjoint A p
  disjoint B n
  disjoint B p
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k r
  disjoint k t
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint m t
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n q
  disjoint n r
  disjoint n t
  disjoint n x
  disjoint n y
  disjoint p q
  disjoint p r
  disjoint p t
  disjoint p x
  disjoint p y
  disjoint q r
  disjoint q t
  disjoint q x
  disjoint q y
  disjoint A q
  disjoint r t
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B k
  disjoint B m
  disjoint B q
  disjoint B r
  disjoint B t
  disjoint B x
  disjoint B y
  assert |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A = B <-> A. p e. Prime A. n e. NN ( ( p ^ n ) || A <-> ( p ^ n ) || B ) ) )

  proof
    cA
    cn0
    wcel
    #
    cB
    cn0
    wcel
    #
    wa
    cA
    cB
    wceq
    #
    vp
    cv
    #
    vn
    cv
    #
    cexp
    co
    #
    cA
    cdvds
    wbr
    #
    @5
    cB
    cdvds
    wbr
    #
    wb
    #
    vn
    cn
    wral
    vp
    cprime
    wral
    #
    @2
    @8
    vp
    vn
    cprime
    cn
    @2
    @8
    @3
    cprime
    wcel
    #
    @4
    cn
    wcel
    wa
    cA
    cB
    @5
    cdvds
    breq2
    a1d
    ralrimivv
    @0
    cA
    cn
    wcel
    #
    cA
    cc0
    wceq
    #
    wo
    #
    @1
    @9
    @2
    wi
    #
    cA
    elnn0
    @13
    @1
    @14
    @11
    @1
    @14
    wi
    @12
    @1
    @11
    @14
    @1
    cB
    cn
    wcel
    #
    cB
    cc0
    wceq
    #
    wo
    #
    @11
    @14
    wi
    #
    cB
    elnn0
    #
    @15
    @18
    @16
    @15
    @11
    @14
    @15
    @11
    wa
    #
    @2
    @9
    @20
    cA
    cB
    wne
    #
    @8
    wn
    #
    vn
    cn
    wrex
    vp
    cprime
    wrex
    #
    @2
    wn
    @9
    wn
    @20
    @21
    cA
    cB
    clt
    wbr
    #
    cB
    cA
    clt
    wbr
    #
    wo
    #
    @23
    @11
    @15
    @21
    @26
    wb
    #
    @11
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @27
    @15
    cA
    nnre
    #
    cB
    nnre
    #
    cA
    cB
    lttri2
    syl2an
    ancoms
    @20
    @24
    @23
    @25
    @15
    vk
    cv
    #
    cB
    clt
    wbr
    #
    @5
    @32
    cdvds
    wbr
    #
    @7
    wb
    #
    wn
    #
    vn
    cn
    wrex
    vp
    cprime
    wrex
    #
    wi
    #
    vk
    cn
    wral
    @11
    @24
    @23
    wi
    #
    cB
    vk
    vn
    vp
    nn0prpwlem
    @38
    @39
    vk
    cA
    cn
    @32
    cA
    wceq
    #
    @33
    @24
    @37
    @23
    @32
    cA
    cB
    clt
    breq1
    @40
    @36
    @22
    vp
    vn
    cprime
    cn
    @40
    @35
    @8
    @40
    @34
    @6
    @7
    @32
    cA
    @5
    cdvds
    breq2
    bibi1d
    notbid
    2rexbidv
    imbi12d
    rspcv
    mpan9
    @11
    @15
    @25
    @23
    wi
    #
    @11
    @32
    cA
    clt
    wbr
    #
    @34
    @6
    wb
    #
    wn
    #
    vn
    cn
    wrex
    vp
    cprime
    wrex
    #
    wi
    #
    vk
    cn
    wral
    @15
    @41
    cA
    vk
    vn
    vp
    nn0prpwlem
    @46
    @41
    vk
    cB
    cn
    @32
    cB
    wceq
    #
    @42
    @25
    @45
    @23
    @32
    cB
    cA
    clt
    breq1
    @47
    @44
    @22
    vp
    vn
    cprime
    cn
    @47
    @43
    @8
    @47
    @43
    @7
    @6
    wb
    @8
    @47
    @34
    @7
    @6
    @32
    cB
    @5
    cdvds
    breq2
    bibi1d
    @7
    @6
    bicom
    syl6bb
    notbid
    2rexbidv
    imbi12d
    rspcv
    syl5com
    impcom
    jaod
    sylbid
    cA
    cB
    df-ne
    @8
    vp
    vn
    cprime
    cn
    rexnal2
    3imtr3g
    con4d
    ex
    @11
    @14
    @16
    @6
    @5
    cc0
    cdvds
    wbr
    #
    wb
    #
    vn
    cn
    wral
    vp
    cprime
    wral
    #
    @12
    wi
    @11
    @50
    @12
    @11
    @49
    wn
    #
    vn
    cn
    wrex
    #
    vp
    cprime
    wrex
    #
    @50
    wn
    @11
    cA
    @3
    clt
    wbr
    #
    vp
    cprime
    wrex
    @53
    cA
    vp
    prmunb
    @11
    @54
    @52
    vp
    cprime
    @11
    @10
    @54
    @52
    @11
    @10
    @54
    w3a
    #
    c1
    cn
    wcel
    #
    @3
    c1
    cexp
    co
    #
    cA
    cdvds
    wbr
    #
    @57
    cc0
    cdvds
    wbr
    #
    wb
    #
    wn
    #
    @52
    1nn
    @55
    @59
    @58
    wi
    #
    @60
    @55
    @62
    @58
    @11
    @10
    @54
    @58
    wn
    @11
    @10
    wa
    @58
    @54
    @10
    @11
    @58
    @54
    wn
    #
    wi
    @10
    @11
    wa
    #
    @58
    @57
    cA
    cle
    wbr
    #
    @63
    @10
    @57
    cz
    wcel
    #
    @11
    @58
    @65
    wi
    @10
    @3
    cz
    wcel
    c1
    cn0
    wcel
    #
    @66
    @3
    prmz
    1nn0
    @3
    c1
    zexpcl
    sylancl
    #
    @57
    cA
    dvdsle
    sylan
    @64
    @65
    cA
    @57
    clt
    wbr
    #
    wn
    #
    @63
    @10
    @57
    cr
    wcel
    #
    @28
    @65
    @70
    wb
    @11
    @10
    @3
    cr
    wcel
    #
    @67
    @71
    @10
    @3
    cn
    wcel
    @72
    @3
    prmnn
    #
    @3
    nnre
    syl
    1nn0
    @3
    c1
    reexpcl
    sylancl
    #
    @30
    @57
    cA
    lenlt
    syl2an
    @64
    @69
    @54
    @64
    @57
    @3
    cA
    clt
    @10
    @57
    @3
    wceq
    #
    @11
    @10
    @3
    @10
    @3
    @73
    nncnd
    exp1d
    #
    adantr
    breq2d
    notbid
    bitrd
    sylibd
    ancoms
    con2d
    3impia
    @55
    @62
    @59
    @58
    @10
    @11
    @59
    @54
    @10
    @66
    @59
    @68
    @57
    dvds0
    syl
    #
    3ad2ant2
    @55
    @62
    idd
    mpid
    mtod
    @58
    @59
    biimpr
    nsyl
    @51
    @61
    vn
    c1
    cn
    @4
    c1
    wceq
    #
    @49
    @60
    @78
    @6
    @58
    @48
    @59
    @78
    @5
    @57
    cA
    cdvds
    @4
    c1
    @3
    cexp
    oveq2
    #
    breq1d
    @78
    @5
    @57
    cc0
    cdvds
    @79
    breq1d
    #
    bibi12d
    notbid
    rspcev
    sylancr
    3expia
    reximdva
    mpd
    @49
    vp
    vn
    cprime
    cn
    rexnal2
    sylib
    pm2.21d
    @16
    @9
    @50
    @2
    @12
    @16
    @8
    @49
    vp
    vn
    cprime
    cn
    @16
    @7
    @48
    @6
    cB
    cc0
    @5
    cdvds
    breq2
    bibi2d
    2ralbidv
    cB
    cc0
    cA
    eqeq2
    imbi12d
    syl5ibr
    jaoi
    sylbi
    com12
    @1
    @14
    @12
    @48
    @7
    wb
    #
    vn
    cn
    wral
    vp
    cprime
    wral
    #
    cc0
    cB
    wceq
    #
    wi
    @1
    @82
    @16
    @83
    @1
    @16
    @82
    @1
    @16
    wn
    #
    @15
    wi
    #
    @84
    @82
    wn
    #
    wi
    @1
    @17
    @16
    @15
    wo
    @85
    @19
    @15
    @16
    orcom
    @16
    @15
    df-or
    3bitri
    @15
    @86
    @84
    @15
    @81
    wn
    #
    vn
    cn
    wrex
    #
    vp
    cprime
    wrex
    #
    @86
    @15
    cB
    @3
    clt
    wbr
    #
    vp
    cprime
    wrex
    @89
    cB
    vp
    prmunb
    @15
    @90
    @88
    vp
    cprime
    @15
    @10
    @90
    @88
    @15
    @10
    @90
    w3a
    #
    @56
    @59
    @57
    cB
    cdvds
    wbr
    #
    wb
    #
    wn
    #
    @88
    1nn
    @91
    @59
    @92
    wi
    #
    @93
    @91
    @95
    @92
    @15
    @10
    @90
    @92
    wn
    @15
    @10
    wa
    @92
    @90
    @10
    @15
    @92
    @90
    wn
    #
    wi
    @10
    @15
    wa
    #
    @92
    @57
    cB
    cle
    wbr
    #
    @96
    @10
    @66
    @15
    @92
    @98
    wi
    @68
    @57
    cB
    dvdsle
    sylan
    @97
    @98
    cB
    @57
    clt
    wbr
    #
    wn
    #
    @96
    @10
    @71
    @29
    @98
    @100
    wb
    @15
    @74
    @31
    @57
    cB
    lenlt
    syl2an
    @97
    @99
    @90
    @97
    @57
    @3
    cB
    clt
    @10
    @75
    @15
    @76
    adantr
    breq2d
    notbid
    bitrd
    sylibd
    ancoms
    con2d
    3impia
    @91
    @95
    @59
    @92
    @10
    @15
    @59
    @90
    @77
    3ad2ant2
    @91
    @95
    idd
    mpid
    mtod
    @59
    @92
    biimp
    nsyl
    @87
    @94
    vn
    c1
    cn
    @78
    @81
    @93
    @78
    @48
    @59
    @7
    @92
    @80
    @78
    @5
    @57
    cB
    cdvds
    @79
    breq1d
    bibi12d
    notbid
    rspcev
    sylancr
    3expia
    reximdva
    mpd
    @81
    vp
    vn
    cprime
    cn
    rexnal2
    sylib
    imim2i
    sylbi
    con4d
    cB
    cc0
    eqcom
    syl6ib
    @12
    @9
    @82
    @2
    @83
    @12
    @8
    @81
    vp
    vn
    cprime
    cn
    @12
    @6
    @48
    @7
    cA
    cc0
    @5
    cdvds
    breq2
    bibi1d
    2ralbidv
    cA
    cc0
    cB
    eqeq1
    imbi12d
    syl5ibr
    jaoi
    imp
    sylanb
    impbid2
end
