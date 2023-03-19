include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "cab.mm"
include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "w3a.mm"
include "cc0.mm"
include "wa.mm"
include "simp2bi.mm"
include "suprcl.mm"
include "syl.mm"
include "simp3bi.mm"
include "cc.mm"
include "recn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "wex.mm"
include "simp2d.mm"
include "n0.mm"
include "sylib.mm"
include "0red.mm"
include "simp1d.mm"
include "sselda.mm"
include "adantr.mm"
include "wi.mm"
include "simp1r.mm"
include "sylbi.mm"
include "breq2.mm"
include "rspccv.mm"
include "imp.mm"
include "suprub.mm"
include "sylan.mm"
include "letrd.mm"
include "exlimddv.mm"
include "simp1l.mm"
include "eqid.mm"
include "biid.mm"
include "supmul1.mm"
include "syl31anc.mm"
include "eqtrd.mm"
include "vex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "rspe.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "2rexbidv.mm"
include "syl5bb.mm"
include "elab2.mm"
include "sylibr.mm"
include "ex.mm"
include "supmullem2.mm"
include "sylan9r.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "wb.mm"
include "adantlr.mm"
include "remulcld.mm"
include "eleq1a.mm"
include "rexlimdva.mm"
include "abssdv.mm"
include "ovex.mm"
include "isseti.mm"
include "rgenw.mm"
include "r19.2z.mm"
include "sylancl.mm"
include "rexcom4.mm"
include "cbvexv.mm"
include "abn0.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "suprleub.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "supmullem1.mm"
include "letri3d.mm"
include "mpbir2and.mm"

theorem supmul
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let vb: setvar b
  let va: setvar a
  let vw: setvar w
  assume supmul.1: |- C = { z | E. v e. A E. b e. B z = ( v x. b ) }
  assume supmul.2: |- ( ph <-> ( ( A. x e. A 0 <_ x /\ A. x e. B 0 <_ x ) /\ ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A y <_ x ) /\ ( B C_ RR /\ B =/= (/) /\ E. x e. RR A. y e. B y <_ x ) ) )

  disjoint A b
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B b
  disjoint B v
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint b ph
  disjoint ph z
  disjoint A a
  disjoint A w
  disjoint a b
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a w
  disjoint a z
  disjoint b w
  disjoint v w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B a
  disjoint B w
  disjoint C a
  disjoint C w
  disjoint a ph
  disjoint ph w
  assert |- ( ph -> ( sup ( A , RR , < ) x. sup ( B , RR , < ) ) = sup ( C , RR , < ) )

  proof
    wph
    cA
    cr
    clt
    csup
    #
    cB
    cr
    clt
    csup
    #
    cmul
    co
    #
    cC
    cr
    clt
    csup
    #
    wceq
    @2
    @3
    cle
    wbr
    @3
    @2
    cle
    wbr
    #
    wph
    @2
    vz
    cv
    #
    @1
    va
    cv
    #
    cmul
    co
    #
    wceq
    #
    va
    cA
    wrex
    #
    vz
    cab
    #
    cr
    clt
    csup
    #
    @3
    cle
    wph
    @2
    @1
    @0
    cmul
    co
    #
    @11
    wph
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @2
    @12
    wceq
    #
    wph
    cA
    cr
    wss
    #
    cA
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
    #
    vy
    cA
    wral
    vx
    cr
    wrex
    #
    w3a
    #
    @13
    wph
    cc0
    @18
    cle
    wbr
    #
    vx
    cA
    wral
    #
    @22
    vx
    cB
    wral
    #
    wa
    #
    @21
    cB
    cr
    wss
    #
    cB
    c0
    wne
    #
    @19
    vy
    cB
    wral
    vx
    cr
    wrex
    #
    w3a
    #
    supmul.2
    simp2bi
    #
    vx
    vy
    cA
    suprcl
    syl
    #
    wph
    @29
    @14
    wph
    @25
    @21
    @29
    supmul.2
    simp3bi
    #
    vx
    vy
    cB
    suprcl
    syl
    #
    @13
    @0
    cc
    wcel
    @1
    cc
    wcel
    #
    @15
    @14
    @0
    recn
    @1
    recn
    #
    @0
    @1
    mulcom
    syl2an
    syl2anc
    wph
    @14
    cc0
    @1
    cle
    wbr
    #
    @23
    @21
    @12
    @11
    wceq
    @33
    wph
    vb
    cv
    #
    cB
    wcel
    #
    @36
    vb
    wph
    @27
    @38
    vb
    wex
    wph
    @26
    @27
    @28
    @32
    simp2d
    #
    vb
    cB
    n0
    sylib
    wph
    @38
    wa
    #
    cc0
    @37
    @1
    @40
    0red
    wph
    cB
    cr
    @37
    wph
    @26
    @27
    @28
    @32
    simp1d
    sselda
    #
    wph
    @14
    @38
    @33
    adantr
    wph
    @38
    cc0
    @37
    cle
    wbr
    #
    wph
    @24
    @38
    @42
    wi
    wph
    @25
    @21
    @29
    w3a
    #
    @24
    supmul.2
    @23
    @24
    @21
    @29
    simp1r
    sylbi
    #
    @22
    @42
    vx
    @37
    cB
    @18
    @37
    cc0
    cle
    breq2
    rspccv
    syl
    imp
    wph
    @29
    @38
    @37
    @1
    cle
    wbr
    @32
    vx
    vy
    cB
    @37
    suprub
    sylan
    letrd
    exlimddv
    wph
    @43
    @23
    supmul.2
    @23
    @24
    @21
    @29
    simp1l
    sylbi
    #
    @30
    @14
    @36
    @23
    w3a
    @21
    wa
    #
    vx
    vy
    vz
    va
    @1
    cA
    @10
    @10
    eqid
    @46
    biid
    supmul1
    syl31anc
    eqtrd
    wph
    @11
    @3
    cle
    wbr
    #
    vw
    cv
    #
    @3
    cle
    wbr
    #
    vw
    @10
    wral
    #
    wph
    @49
    vw
    @10
    @48
    @10
    wcel
    @48
    @7
    wceq
    #
    va
    cA
    wrex
    #
    wph
    @49
    @9
    @52
    vz
    @48
    vw
    vex
    #
    @5
    @48
    wceq
    #
    @8
    @51
    va
    cA
    @5
    @48
    @7
    eqeq1
    rexbidv
    elab
    wph
    @51
    @49
    va
    cA
    wph
    @6
    cA
    wcel
    #
    wa
    #
    @49
    @51
    @7
    @3
    cle
    wbr
    @56
    @7
    @6
    @1
    cmul
    co
    #
    @3
    cle
    @56
    @14
    @6
    cr
    wcel
    #
    @7
    @57
    wceq
    #
    wph
    @14
    @55
    @33
    adantr
    #
    wph
    cA
    cr
    @6
    wph
    @16
    @17
    @20
    @30
    simp1d
    sselda
    #
    @14
    @34
    @6
    cc
    wcel
    @59
    @58
    @35
    @6
    recn
    @1
    @6
    mulcom
    syl2an
    syl2anc
    @56
    @57
    @5
    @6
    @37
    cmul
    co
    #
    wceq
    #
    vb
    cB
    wrex
    #
    vz
    cab
    #
    cr
    clt
    csup
    #
    @3
    cle
    @56
    @58
    cc0
    @6
    cle
    wbr
    #
    @24
    @29
    @57
    @66
    wceq
    @61
    wph
    @55
    @67
    wph
    @23
    @55
    @67
    wi
    @45
    @22
    @67
    vx
    @6
    cA
    @18
    @6
    cc0
    cle
    breq2
    rspccv
    syl
    imp
    wph
    @24
    @55
    @44
    adantr
    wph
    @29
    @55
    @32
    adantr
    @58
    @67
    @24
    w3a
    @29
    wa
    #
    vx
    vy
    vz
    vb
    @6
    cB
    @65
    @65
    eqid
    @68
    biid
    supmul1
    syl31anc
    @56
    @66
    @3
    cle
    wbr
    #
    @49
    vw
    @65
    wral
    #
    @56
    @49
    vw
    @65
    @48
    @65
    wcel
    @48
    @62
    wceq
    #
    vb
    cB
    wrex
    #
    @56
    @49
    @64
    @72
    vz
    @48
    @53
    @54
    @63
    @71
    vb
    cB
    @5
    @48
    @62
    eqeq1
    #
    rexbidv
    #
    elab
    @55
    @72
    @48
    cC
    wcel
    #
    wph
    @49
    @55
    @72
    @75
    @55
    @72
    wa
    @72
    va
    cA
    wrex
    #
    @75
    @72
    va
    cA
    rspe
    @5
    vv
    cv
    #
    @37
    cmul
    co
    #
    wceq
    #
    vb
    cB
    wrex
    #
    vv
    cA
    wrex
    #
    @76
    vz
    @48
    cC
    @53
    @81
    @64
    va
    cA
    wrex
    @54
    @76
    @80
    @64
    vv
    va
    cA
    @77
    @6
    wceq
    #
    @79
    @63
    vb
    cB
    @82
    @78
    @62
    @5
    @77
    @6
    @37
    cmul
    oveq1
    eqeq2d
    rexbidv
    cbvrexv
    @54
    @63
    @71
    va
    vb
    cA
    cB
    @73
    2rexbidv
    syl5bb
    supmul.1
    elab2
    sylibr
    ex
    wph
    cC
    cr
    wss
    cC
    c0
    wne
    @48
    @18
    cle
    wbr
    #
    vw
    cC
    wral
    vx
    cr
    wrex
    w3a
    #
    @75
    @49
    wi
    wph
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    cC
    vb
    supmul.1
    supmul.2
    supmullem2
    #
    @84
    @75
    @49
    vx
    vw
    cC
    @48
    suprub
    ex
    syl
    sylan9r
    syl5bi
    ralrimiv
    #
    @56
    @65
    cr
    wss
    @65
    c0
    wne
    #
    @83
    vw
    @65
    wral
    #
    vx
    cr
    wrex
    #
    @3
    cr
    wcel
    #
    @69
    @70
    wb
    @56
    @64
    vz
    cr
    @56
    @63
    @5
    cr
    wcel
    #
    vb
    cB
    @56
    @38
    wa
    #
    @62
    cr
    wcel
    @63
    @91
    wi
    @92
    @6
    @37
    @56
    @58
    @38
    @61
    adantr
    wph
    @38
    @37
    cr
    wcel
    @55
    @41
    adantlr
    remulcld
    @62
    cr
    @5
    eleq1a
    syl
    rexlimdva
    abssdv
    wph
    @87
    @55
    wph
    @64
    vz
    wex
    #
    @87
    wph
    @72
    vw
    wex
    #
    @93
    wph
    @71
    vw
    wex
    #
    vb
    cB
    wrex
    #
    @94
    wph
    @27
    @95
    vb
    cB
    wral
    @96
    @39
    @95
    vb
    cB
    vw
    @62
    @6
    @37
    cmul
    ovex
    isseti
    rgenw
    @95
    vb
    cB
    r19.2z
    sylancl
    @71
    vb
    vw
    cB
    rexcom4
    sylib
    @64
    @72
    vz
    vw
    @74
    cbvexv
    sylibr
    @64
    vz
    abn0
    sylibr
    adantr
    @56
    @90
    @70
    @89
    wph
    @90
    @55
    wph
    @84
    @90
    @85
    vx
    vw
    cC
    suprcl
    syl
    #
    adantr
    #
    @86
    @88
    @70
    vx
    @3
    cr
    @18
    @3
    wceq
    #
    @83
    @49
    vw
    @65
    @18
    @3
    @48
    cle
    breq2
    #
    ralbidv
    rspcev
    syl2anc
    @98
    vx
    vw
    vw
    @65
    @3
    suprleub
    syl31anc
    mpbird
    eqbrtrd
    eqbrtrd
    @48
    @7
    @3
    cle
    breq1
    syl5ibrcom
    rexlimdva
    syl5bi
    ralrimiv
    #
    wph
    @10
    cr
    wss
    @10
    c0
    wne
    #
    @83
    vw
    @10
    wral
    #
    vx
    cr
    wrex
    #
    @90
    @47
    @50
    wb
    wph
    @9
    vz
    cr
    wph
    @8
    @91
    va
    cA
    @56
    @7
    cr
    wcel
    @8
    @91
    wi
    @56
    @1
    @6
    @60
    @61
    remulcld
    @7
    cr
    @5
    eleq1a
    syl
    rexlimdva
    abssdv
    wph
    @9
    vz
    wex
    #
    @102
    wph
    @8
    vz
    wex
    #
    va
    cA
    wrex
    #
    @105
    wph
    @17
    @106
    va
    cA
    wral
    @107
    wph
    @16
    @17
    @20
    @30
    simp2d
    @106
    va
    cA
    vz
    @7
    @1
    @6
    cmul
    ovex
    isseti
    rgenw
    @106
    va
    cA
    r19.2z
    sylancl
    @8
    va
    vz
    cA
    rexcom4
    sylib
    @9
    vz
    abn0
    sylibr
    wph
    @90
    @50
    @104
    @97
    @101
    @103
    @50
    vx
    @3
    cr
    @99
    @83
    @49
    vw
    @10
    @100
    ralbidv
    rspcev
    syl2anc
    @97
    vx
    vw
    vw
    @10
    @3
    suprleub
    syl31anc
    mpbird
    eqbrtrd
    wph
    @4
    @48
    @2
    cle
    wbr
    vw
    cC
    wral
    #
    wph
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    cC
    vb
    supmul.1
    supmul.2
    supmullem1
    wph
    @84
    @2
    cr
    wcel
    @4
    @108
    wb
    @85
    wph
    @0
    @1
    @31
    @33
    remulcld
    #
    vx
    vw
    vw
    cC
    @2
    suprleub
    syl2anc
    mpbird
    wph
    @2
    @3
    @109
    @97
    letri3d
    mpbir2and
end
