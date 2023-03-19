include "wcel.mm"
include "cv.mm"
include "cltr.mm"
include "wbr.mm"
include "wral.mm"
include "cnr.mm"
include "wrex.mm"
include "wa.mm"
include "cltp.mm"
include "wn.mm"
include "wi.mm"
include "cnp.mm"
include "c0.mm"
include "wne.mm"
include "c1p.mm"
include "c0r.mm"
include "cplr.mm"
include "co.mm"
include "wceq.mm"
include "0idsr.mm"
include "mp1i.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "cop.mm"
include "cer.mm"
include "cec.mm"
include "1pr.mm"
include "elexi.mm"
include "opeq1.mm"
include "eceq1d.mm"
include "df-0r.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "elab2.mm"
include "sylibr.mm"
include "ne0i.mm"
include "syl.mm"
include "breq1.mm"
include "rspccv.mm"
include "cm1r.mm"
include "c1r.mm"
include "0lt1sr.mm"
include "wb.mm"
include "m1r.mm"
include "ltasr.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "m1p1sr.mm"
include "3brtr3i.mm"
include "breqtri.mm"
include "ltsosr.mm"
include "ltrelsr.mm"
include "sotri.mm"
include "mpan.mm"
include "map2psrpr.mm"
include "sylib.mm"
include "syl6.mm"
include "breq2.mm"
include "ralbidv.mm"
include "abeq2i.mm"
include "ltpsrpr.mm"
include "syl6ib.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "syl6bir.mm"
include "com12.mm"
include "reximdv.mm"
include "syld.mm"
include "rexlimivw.mm"
include "impcom.mm"
include "supexpr.mm"
include "syl2anc.mm"
include "mappsrpr.mm"
include "brel.mm"
include "sylbir.mm"
include "simprd.mm"
include "adantl.mm"
include "wex.mm"
include "sylanbr.mm"
include "rexex.mm"
include "wal.mm"
include "df-ral.mm"
include "19.29.mm"
include "eleq1.mm"
include "syl5bb.mm"
include "syl5bbr.mm"
include "notbid.mm"
include "imbi12d.mm"
include "biimpac.mm"
include "exlimiv.mm"
include "sylanb.mm"
include "expcom.mm"
include "3syl.mm"
include "impd.mm"
include "impancom.mm"
include "pm2.01d.mm"
include "expr.mm"
include "ex.mm"
include "r19.29.mm"
include "biimprd.mm"
include "vex.mm"
include "syl6bb.mm"
include "rspcev.mm"
include "rexlimiva.mm"
include "rexbidv.mm"
include "syl5ib.mm"
include "imim12d.mm"
include "sylan2b.mm"
include "a1dd.mm"
include "sotri2.mm"
include "mp3an3.mm"
include "syl5.mm"
include "expcomd.mm"
include "ad2antrr.mm"
include "pm2.61d.mm"
include "adantlr.mm"
include "anim12d.mm"
include "imbi1d.mm"
include "anbi12d.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem supsrlem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let vv: setvar v
  let vu: setvar u
  assume supsrlem.1: |- B = { w | ( C +R [ <. w , 1P >. ] ~R ) e. A }
  assume supsrlem.2: |- C e. R.

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint C w
  disjoint v x
  disjoint u x
  disjoint v y
  disjoint u y
  disjoint v z
  disjoint u z
  disjoint v w
  disjoint u w
  disjoint u v
  disjoint A v
  disjoint A u
  disjoint B v
  disjoint B u
  disjoint C v
  disjoint C u
  assert |- ( ( C e. A /\ E. x e. R. A. y e. A y <R x ) -> E. x e. R. ( A. y e. A -. x <R y /\ A. y e. R. ( y <R x -> E. z e. A y <R z ) ) )

  proof
    cC
    cA
    wcel
    #
    vy
    cv
    #
    vx
    cv
    #
    cltr
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cnr
    wrex
    #
    wa
    #
    vv
    cv
    #
    vw
    cv
    #
    cltp
    wbr
    #
    wn
    #
    vw
    cB
    wral
    #
    @8
    @7
    cltp
    wbr
    #
    @8
    vu
    cv
    #
    cltp
    wbr
    #
    vu
    cB
    wrex
    #
    wi
    #
    vw
    cnp
    wral
    #
    wa
    #
    vv
    cnp
    wrex
    #
    @2
    @1
    cltr
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @3
    @1
    vz
    cv
    #
    cltr
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cnr
    wral
    #
    wa
    #
    vx
    cnr
    wrex
    #
    @6
    cB
    c0
    wne
    #
    @12
    vw
    cB
    wral
    #
    vv
    cnp
    wrex
    #
    @19
    @6
    c1p
    cB
    wcel
    #
    @30
    @6
    cC
    c0r
    cplr
    co
    #
    cA
    wcel
    #
    @33
    @6
    @34
    cC
    cA
    cC
    cnr
    wcel
    #
    @34
    cC
    wceq
    #
    @6
    supsrlem.2
    cC
    0idsr
    #
    mp1i
    @0
    @5
    simpl
    eqeltrd
    cC
    @8
    c1p
    cop
    #
    cer
    cec
    #
    cplr
    co
    #
    cA
    wcel
    #
    @35
    vw
    c1p
    cB
    c1p
    cnp
    1pr
    elexi
    @8
    c1p
    wceq
    #
    @41
    @34
    cA
    @43
    @40
    c0r
    cC
    cplr
    @43
    @40
    c1p
    c1p
    cop
    #
    cer
    cec
    c0r
    @43
    @39
    @44
    cer
    @8
    c1p
    c1p
    opeq1
    eceq1d
    df-0r
    syl6eqr
    oveq2d
    eleq1d
    supsrlem.1
    elab2
    sylibr
    cB
    c1p
    ne0i
    syl
    @5
    @0
    @32
    @4
    @0
    @32
    wi
    vx
    cnr
    @4
    @0
    cC
    @7
    c1p
    cop
    cer
    cec
    cplr
    co
    #
    @2
    wceq
    #
    vv
    cnp
    wrex
    #
    @32
    @4
    @0
    cC
    @2
    cltr
    wbr
    #
    @47
    @3
    @48
    vy
    cC
    cA
    @1
    cC
    @2
    cltr
    breq1
    rspccv
    @48
    cC
    cm1r
    cplr
    co
    #
    @2
    cltr
    wbr
    #
    @47
    @49
    cC
    cltr
    wbr
    #
    @48
    @50
    @49
    @34
    cC
    cltr
    cm1r
    c0r
    cltr
    wbr
    #
    @49
    @34
    cltr
    wbr
    #
    cm1r
    c0r
    cplr
    co
    #
    cm1r
    c1r
    cplr
    co
    #
    cm1r
    c0r
    cltr
    c0r
    c1r
    cltr
    wbr
    #
    @54
    @55
    cltr
    wbr
    #
    0lt1sr
    cm1r
    cnr
    wcel
    #
    @56
    @57
    wb
    m1r
    c0r
    c1r
    cm1r
    ltasr
    ax-mp
    mpbi
    @58
    @54
    cm1r
    wceq
    m1r
    cm1r
    0idsr
    ax-mp
    m1p1sr
    3brtr3i
    @36
    @52
    @53
    wb
    supsrlem.2
    cm1r
    c0r
    cC
    ltasr
    ax-mp
    mpbi
    @36
    @37
    supsrlem.2
    @38
    ax-mp
    breqtri
    #
    @49
    cC
    @2
    cltr
    cnr
    ltsosr
    ltrelsr
    sotri
    mpan
    vv
    @2
    cC
    supsrlem.2
    map2psrpr
    sylib
    syl6
    @4
    @46
    @31
    vv
    cnp
    @46
    @4
    @31
    @46
    @4
    @1
    @45
    cltr
    wbr
    #
    vy
    cA
    wral
    #
    @31
    @46
    @60
    @3
    vy
    cA
    @45
    @2
    @1
    cltr
    breq2
    ralbidv
    @61
    @12
    vw
    cB
    @8
    cB
    wcel
    #
    @42
    @61
    @12
    @42
    vw
    cB
    supsrlem.1
    abeq2i
    #
    @61
    @42
    @41
    @45
    cltr
    wbr
    #
    @12
    @60
    @64
    vy
    @41
    cA
    @1
    @41
    @45
    cltr
    breq1
    rspccv
    @8
    @7
    cC
    supsrlem.2
    ltpsrpr
    #
    syl6ib
    syl5bi
    ralrimiv
    syl6bir
    com12
    reximdv
    syld
    rexlimivw
    impcom
    vv
    vw
    vu
    cB
    supexpr
    syl2anc
    @6
    @18
    @29
    vv
    cnp
    @6
    @7
    cnp
    wcel
    #
    wa
    #
    @45
    cnr
    wcel
    #
    @18
    @45
    @1
    cltr
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @60
    @25
    wi
    #
    vy
    cnr
    wral
    #
    wa
    #
    @29
    @66
    @68
    @6
    @66
    @49
    cnr
    wcel
    #
    @68
    @66
    @49
    @45
    cltr
    wbr
    #
    @75
    @68
    wa
    @7
    cC
    supsrlem.2
    mappsrpr
    #
    @49
    @45
    cnr
    cnr
    cltr
    ltrelsr
    brel
    sylbir
    simprd
    adantl
    @67
    @11
    @71
    @17
    @73
    @66
    @11
    @71
    wi
    @6
    @66
    @11
    @71
    @66
    @11
    wa
    @70
    vy
    cA
    @66
    @11
    @1
    cA
    wcel
    #
    @70
    @66
    @11
    @78
    wa
    #
    wa
    @69
    @66
    @69
    @79
    @70
    @66
    @69
    wa
    #
    @11
    @78
    @70
    @80
    @41
    @1
    wceq
    #
    vw
    cnp
    wrex
    #
    @81
    vw
    wex
    #
    @11
    @78
    @70
    wi
    #
    wi
    @80
    @49
    @1
    cltr
    wbr
    #
    @82
    @66
    @76
    @69
    @85
    @77
    @49
    @45
    @1
    cltr
    cnr
    ltsosr
    ltrelsr
    sotri
    sylanbr
    vw
    @1
    cC
    supsrlem.2
    map2psrpr
    #
    sylib
    @81
    vw
    cnp
    rexex
    @11
    @83
    @84
    @11
    @62
    @10
    wi
    #
    vw
    wal
    #
    @83
    @84
    @10
    vw
    cB
    df-ral
    @88
    @83
    wa
    @87
    @81
    wa
    #
    vw
    wex
    @84
    @87
    @81
    vw
    19.29
    @89
    @84
    vw
    @81
    @87
    @84
    @81
    @62
    @78
    @10
    @70
    @62
    @42
    @81
    @78
    @63
    @41
    @1
    cA
    eleq1
    syl5bb
    @81
    @9
    @69
    @9
    @45
    @41
    cltr
    wbr
    @81
    @69
    @7
    @8
    cC
    supsrlem.2
    ltpsrpr
    @41
    @1
    @45
    cltr
    breq2
    syl5bbr
    notbid
    imbi12d
    biimpac
    exlimiv
    syl
    sylanb
    expcom
    3syl
    impd
    impancom
    pm2.01d
    expr
    ralrimiv
    ex
    adantl
    @0
    @66
    @17
    @73
    wi
    @5
    @0
    @66
    wa
    #
    @17
    @73
    @90
    @17
    wa
    #
    @72
    vy
    cnr
    @91
    @85
    @1
    cnr
    wcel
    #
    @72
    wi
    #
    @91
    @85
    @72
    @92
    @17
    @85
    @72
    wi
    @90
    @17
    @85
    @72
    @85
    @17
    @82
    @72
    @86
    @17
    @82
    wa
    @16
    @81
    wa
    #
    vw
    cnp
    wrex
    @72
    @16
    @81
    vw
    cnp
    r19.29
    @94
    @72
    vw
    cnp
    @81
    @16
    @72
    @81
    @60
    @12
    @15
    @25
    @81
    @12
    @60
    @12
    @64
    @81
    @60
    @65
    @41
    @1
    @45
    cltr
    breq1
    syl5bbr
    biimprd
    @15
    @41
    @23
    cltr
    wbr
    #
    vz
    cA
    wrex
    #
    @81
    @25
    @14
    @96
    vu
    cB
    @13
    cB
    wcel
    cC
    @13
    c1p
    cop
    #
    cer
    cec
    #
    cplr
    co
    #
    cA
    wcel
    #
    @14
    @96
    @42
    @100
    vw
    @13
    cB
    vu
    vex
    @8
    @13
    wceq
    #
    @41
    @99
    cA
    @101
    @40
    @98
    cC
    cplr
    @101
    @39
    @97
    cer
    @8
    @13
    c1p
    opeq1
    eceq1d
    oveq2d
    eleq1d
    supsrlem.1
    elab2
    @95
    @14
    vz
    @99
    cA
    @23
    @99
    wceq
    @95
    @41
    @99
    cltr
    wbr
    @14
    @23
    @99
    @41
    cltr
    breq2
    @8
    @13
    cC
    supsrlem.2
    ltpsrpr
    syl6bb
    rspcev
    sylanb
    rexlimiva
    @81
    @95
    @24
    vz
    cA
    @41
    @1
    @23
    cltr
    breq1
    rexbidv
    syl5ib
    imim12d
    impcom
    rexlimivw
    syl
    sylan2b
    ex
    adantl
    a1dd
    @0
    @85
    wn
    #
    @93
    wi
    @66
    @17
    @0
    @92
    @102
    @72
    @92
    @102
    wa
    @1
    cC
    cltr
    wbr
    #
    @0
    @72
    @92
    @102
    @51
    @103
    @59
    @1
    @49
    cC
    cltr
    cnr
    ltsosr
    ltrelsr
    sotri2
    mp3an3
    @0
    @103
    @25
    @60
    @0
    @103
    @25
    @24
    @103
    vz
    cC
    cA
    @23
    cC
    @1
    cltr
    breq2
    rspcev
    ex
    a1dd
    syl5
    expcomd
    ad2antrr
    pm2.61d
    ralrimiv
    ex
    adantlr
    anim12d
    @28
    @74
    vx
    @45
    cnr
    @2
    @45
    wceq
    #
    @22
    @71
    @27
    @73
    @104
    @21
    @70
    vy
    cA
    @104
    @20
    @69
    @2
    @45
    @1
    cltr
    breq1
    notbid
    ralbidv
    @104
    @26
    @72
    vy
    cnr
    @104
    @3
    @60
    @25
    @2
    @45
    @1
    cltr
    breq2
    imbi1d
    ralbidv
    anbi12d
    rspcev
    syl6an
    rexlimdva
    mpd
end
