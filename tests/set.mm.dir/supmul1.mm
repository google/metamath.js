include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "wrex.mm"
include "vex.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "elab2.mm"
include "cc0.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "simpr.mm"
include "sylbi.mm"
include "simp1d.mm"
include "sselda.mm"
include "suprcl.mm"
include "syl.mm"
include "adantr.mm"
include "simpl1.mm"
include "simpl2.mm"
include "jca.mm"
include "suprub.mm"
include "sylan.mm"
include "lemul2a.mm"
include "syl31anc.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "wb.mm"
include "wi.mm"
include "remulcld.mm"
include "eleq1a.mm"
include "ssrdv.mm"
include "wex.mm"
include "simpr2.mm"
include "ovex.mm"
include "isseti.mm"
include "rgenw.mm"
include "r19.2z.mm"
include "sylancl.mm"
include "exbii.mm"
include "n0.mm"
include "rexcom4.mm"
include "3bitr4i.mm"
include "sylibr.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "3jca.mm"
include "suprleub.mm"
include "mpbird.mm"
include "cdiv.mm"
include "0red.mm"
include "simpl3.mm"
include "rspccva.mm"
include "letrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpd.mm"
include "imp.mm"
include "mulge0d.mm"
include "anim1i.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "prodgt02.mm"
include "syl22anc.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "gt0ne0d.mm"
include "redivcld.mm"
include "suprlub.mm"
include "mpbid.mm"
include "rspe.mm"
include "adantl.mm"
include "simplrr.mm"
include "adantlr.mm"
include "eqbrtrrd.mm"
include "mpdan.mm"
include "expr.mm"
include "mpi.mm"
include "ad2antrr.mm"
include "lenltd.mm"
include "mtbird.mm"
include "nrexdv.mm"
include "pm2.65da.mm"
include "eqleltd.mm"
include "eqcomd.mm"

theorem supmul1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let vb: setvar b
  let vw: setvar w
  assume supmul1.1: |- C = { z | E. v e. B z = ( A x. v ) }
  assume supmul1.2: |- ( ph <-> ( ( A e. RR /\ 0 <_ A /\ A. x e. B 0 <_ x ) /\ ( B C_ RR /\ B =/= (/) /\ E. x e. RR A. y e. B y <_ x ) ) )

  disjoint A v
  disjoint A x
  disjoint A z
  disjoint v x
  disjoint v z
  disjoint x z
  disjoint B v
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint v y
  disjoint x y
  disjoint y z
  disjoint C x
  disjoint A b
  disjoint A w
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b z
  disjoint v w
  disjoint w x
  disjoint w z
  disjoint B b
  disjoint B w
  disjoint b y
  disjoint w y
  disjoint C b
  disjoint C w
  disjoint b ph
  disjoint ph w
  assert |- ( ph -> ( A x. sup ( B , RR , < ) ) = sup ( C , RR , < ) )

  proof
    wph
    cC
    cr
    clt
    csup
    #
    cA
    cB
    cr
    clt
    csup
    #
    cmul
    co
    #
    wph
    @0
    @2
    wceq
    @0
    @2
    cle
    wbr
    #
    @0
    @2
    clt
    wbr
    #
    wn
    #
    wa
    wph
    @3
    @5
    wph
    @3
    vw
    cv
    #
    @2
    cle
    wbr
    #
    vw
    cC
    wral
    #
    wph
    @7
    vw
    cC
    @6
    cC
    wcel
    #
    @6
    cA
    vb
    cv
    #
    cmul
    co
    #
    wceq
    #
    vb
    cB
    wrex
    #
    wph
    @7
    vz
    cv
    #
    cA
    vv
    cv
    #
    cmul
    co
    #
    wceq
    #
    vv
    cB
    wrex
    #
    @13
    vz
    @6
    cC
    vw
    vex
    @18
    @14
    @11
    wceq
    #
    vb
    cB
    wrex
    @14
    @6
    wceq
    #
    @13
    @17
    @19
    vv
    vb
    cB
    @15
    @10
    wceq
    @16
    @11
    @14
    @15
    @10
    cA
    cmul
    oveq2
    eqeq2d
    cbvrexv
    @20
    @19
    @12
    vb
    cB
    @14
    @6
    @11
    eqeq1
    rexbidv
    syl5bb
    supmul1.1
    elab2
    #
    wph
    @12
    @7
    vb
    cB
    wph
    @10
    cB
    wcel
    #
    wa
    #
    @7
    @12
    @11
    @2
    cle
    wbr
    #
    @23
    @10
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    @10
    @1
    cle
    wbr
    #
    @24
    wph
    cB
    cr
    @10
    wph
    cB
    cr
    wss
    #
    cB
    c0
    wne
    #
    vy
    cv
    vx
    cv
    #
    cle
    wbr
    vy
    cB
    wral
    vx
    cr
    wrex
    #
    wph
    @27
    @28
    cc0
    @33
    cle
    wbr
    #
    vx
    cB
    wral
    #
    w3a
    #
    @31
    @32
    @34
    w3a
    #
    wa
    #
    @38
    supmul1.2
    @37
    @38
    simpr
    sylbi
    #
    simp1d
    sselda
    #
    wph
    @26
    @22
    wph
    @38
    @26
    @40
    vx
    vy
    cB
    suprcl
    syl
    #
    adantr
    #
    wph
    @29
    @22
    wph
    @27
    @28
    wph
    @39
    @27
    supmul1.2
    @27
    @28
    @36
    @38
    simpl1
    sylbi
    #
    wph
    @39
    @28
    supmul1.2
    @27
    @28
    @36
    @38
    simpl2
    sylbi
    #
    jca
    adantr
    wph
    @38
    @22
    @30
    @40
    vx
    vy
    cB
    @10
    suprub
    sylan
    #
    @10
    @1
    cA
    lemul2a
    syl31anc
    @6
    @11
    @2
    cle
    breq1
    syl5ibrcom
    rexlimdva
    syl5bi
    ralrimiv
    #
    wph
    cC
    cr
    wss
    #
    cC
    c0
    wne
    #
    @6
    @33
    cle
    wbr
    #
    vw
    cC
    wral
    #
    vx
    cr
    wrex
    #
    w3a
    #
    @2
    cr
    wcel
    #
    @3
    @8
    wb
    wph
    @48
    @49
    @52
    wph
    vw
    cC
    cr
    @9
    @13
    wph
    @6
    cr
    wcel
    #
    @21
    wph
    @12
    @55
    vb
    cB
    @23
    @11
    cr
    wcel
    #
    @12
    @55
    wi
    @23
    cA
    @10
    wph
    @27
    @22
    @44
    adantr
    #
    @41
    remulcld
    #
    @11
    cr
    @6
    eleq1a
    syl
    rexlimdva
    syl5bi
    #
    ssrdv
    wph
    @12
    vw
    wex
    #
    vb
    cB
    wrex
    #
    @49
    wph
    @32
    @60
    vb
    cB
    wral
    @61
    wph
    @39
    @32
    supmul1.2
    @37
    @31
    @32
    @34
    simpr2
    sylbi
    #
    @60
    vb
    cB
    vw
    @11
    cA
    @10
    cmul
    ovex
    isseti
    #
    rgenw
    @60
    vb
    cB
    r19.2z
    sylancl
    @9
    vw
    wex
    #
    @13
    vw
    wex
    @49
    @61
    @9
    @13
    vw
    @21
    exbii
    vw
    cC
    n0
    #
    @12
    vb
    vw
    cB
    rexcom4
    3bitr4i
    sylibr
    #
    wph
    @54
    @8
    @52
    wph
    cA
    @1
    @44
    @42
    remulcld
    #
    @47
    @51
    @8
    vx
    @2
    cr
    @33
    @2
    wceq
    @50
    @7
    vw
    cC
    @33
    @2
    @6
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    3jca
    #
    @67
    vx
    vw
    vw
    cC
    @2
    suprleub
    syl2anc
    mpbird
    wph
    @4
    @0
    cA
    cdiv
    co
    #
    @10
    clt
    wbr
    #
    vb
    cB
    wrex
    #
    wph
    @4
    wa
    #
    @69
    @1
    clt
    wbr
    #
    @71
    @72
    @73
    @4
    wph
    @4
    simpr
    @72
    @0
    cr
    wcel
    #
    @26
    @27
    cc0
    cA
    clt
    wbr
    #
    @73
    @4
    wb
    wph
    @74
    @4
    wph
    @53
    @74
    @68
    vx
    vw
    cC
    suprcl
    syl
    #
    adantr
    #
    wph
    @26
    @4
    @42
    adantr
    #
    wph
    @27
    @4
    @44
    adantr
    #
    @72
    @27
    @26
    cc0
    @1
    cle
    wbr
    #
    cc0
    @2
    clt
    wbr
    #
    @75
    @79
    @78
    wph
    @80
    @4
    wph
    @32
    @80
    @62
    @32
    @22
    vb
    wex
    wph
    @80
    vb
    cB
    n0
    wph
    @22
    @80
    vb
    wph
    @22
    @80
    @23
    cc0
    @10
    @1
    @23
    0red
    @41
    @43
    wph
    @36
    @22
    cc0
    @10
    cle
    wbr
    #
    wph
    @39
    @36
    supmul1.2
    @27
    @28
    @36
    @38
    simpl3
    sylbi
    @35
    @82
    vx
    @10
    cB
    @33
    @10
    cc0
    cle
    breq2
    rspccva
    sylan
    #
    @46
    letrd
    ex
    exlimdv
    syl5bi
    mpd
    adantr
    @72
    cc0
    @0
    cle
    wbr
    #
    @4
    wa
    #
    @81
    wph
    @84
    @4
    wph
    @49
    @84
    @66
    @49
    @64
    wph
    @84
    @65
    wph
    @9
    @84
    vw
    wph
    @9
    @84
    wph
    @9
    wa
    #
    cc0
    @6
    @0
    @86
    0red
    wph
    @9
    @55
    @59
    imp
    wph
    @74
    @9
    @76
    adantr
    wph
    @9
    cc0
    @6
    cle
    wbr
    #
    @9
    @13
    wph
    @87
    @21
    wph
    @12
    @87
    vb
    cB
    @23
    @87
    @12
    cc0
    @11
    cle
    wbr
    @23
    cA
    @10
    @57
    @41
    wph
    @28
    @22
    @45
    adantr
    @83
    mulge0d
    @6
    @11
    cc0
    cle
    breq2
    syl5ibrcom
    rexlimdva
    syl5bi
    imp
    wph
    @53
    @9
    @6
    @0
    cle
    wbr
    #
    @68
    vx
    vw
    cC
    @6
    suprub
    sylan
    #
    letrd
    ex
    exlimdv
    syl5bi
    mpd
    anim1i
    wph
    @85
    @81
    wi
    #
    @4
    wph
    cc0
    cr
    wcel
    @74
    @54
    @90
    wph
    0red
    @76
    @67
    cc0
    @0
    @2
    lelttr
    syl3anc
    adantr
    mpd
    cA
    @1
    prodgt02
    syl22anc
    #
    @0
    @1
    cA
    ltdivmul
    syl112anc
    mpbird
    @72
    @38
    @69
    cr
    wcel
    @73
    @71
    wb
    wph
    @38
    @4
    @40
    adantr
    @72
    @0
    cA
    @77
    @79
    @72
    cA
    @91
    gt0ne0d
    redivcld
    vx
    vy
    vb
    cB
    @69
    suprlub
    syl2anc
    mpbid
    @72
    @70
    vb
    cB
    @72
    @22
    wa
    #
    @70
    @0
    @11
    clt
    wbr
    #
    @92
    @11
    @0
    cle
    wbr
    #
    @93
    wn
    wph
    @22
    @94
    @4
    @23
    @60
    @94
    @63
    @23
    @12
    @94
    vw
    wph
    @22
    @12
    @94
    wph
    @22
    @12
    wa
    #
    wa
    #
    @9
    @94
    @95
    @9
    wph
    @95
    @13
    @9
    @12
    vb
    cB
    rspe
    @21
    sylibr
    adantl
    @96
    @9
    wa
    @6
    @11
    @0
    cle
    wph
    @22
    @12
    @9
    simplrr
    wph
    @9
    @88
    @95
    @89
    adantlr
    eqbrtrrd
    mpdan
    expr
    exlimdv
    mpi
    adantlr
    @92
    @11
    @0
    wph
    @22
    @56
    @4
    @58
    adantlr
    wph
    @74
    @4
    @22
    @76
    ad2antrr
    #
    lenltd
    mpbid
    @92
    @74
    @25
    @27
    @75
    @70
    @93
    wb
    @97
    wph
    @22
    @25
    @4
    @41
    adantlr
    wph
    @27
    @4
    @22
    @44
    ad2antrr
    @72
    @75
    @22
    @91
    adantr
    @0
    @10
    cA
    ltdivmul
    syl112anc
    mtbird
    nrexdv
    pm2.65da
    jca
    wph
    @0
    @2
    @76
    @67
    eqleltd
    mpbird
    eqcomd
end
