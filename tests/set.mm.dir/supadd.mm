include "cr.mm"
include "clt.mm"
include "csup.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "cab.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wcel.mm"
include "suprcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "supaddc.mm"
include "wa.mm"
include "sselda.mm"
include "recnd.mm"
include "adantr.mm"
include "addcomd.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "abbidv.mm"
include "supeq1d.mm"
include "eqtrd.mm"
include "vex.mm"
include "weq.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "adantlr.mm"
include "rspe.mm"
include "oveq1.mm"
include "cbvrexv.mm"
include "2rexbidv.mm"
include "syl5bb.mm"
include "elab2.mm"
include "sylibr.mm"
include "ex.mm"
include "wi.mm"
include "sseld.mm"
include "anim12d.mm"
include "readdcl.mm"
include "syl6.mm"
include "eleq1a.mm"
include "rexlimdvv.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "wex.mm"
include "ovex.mm"
include "isseti.mm"
include "rgenw.mm"
include "r19.2z.mm"
include "sylancl.mm"
include "rexcom4.mm"
include "sylib.mm"
include "ralrimivw.mm"
include "syl2anc.mm"
include "n0.mm"
include "exbii.mm"
include "bitri.mm"
include "readdcld.mm"
include "adantrr.mm"
include "adantrl.mm"
include "w3a.mm"
include "3jca.mm"
include "suprub.mm"
include "sylan.mm"
include "le2addd.mm"
include "breq1.mm"
include "biimprcd.mm"
include "ralrimiv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylan9r.mm"
include "wb.mm"
include "syl.mm"
include "rexlimdva.mm"
include "abssdv.mm"
include "abn0.mm"
include "suprleub.mm"
include "syl31anc.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "syl5ibrcom.mm"
include "letri3d.mm"
include "mpbir2and.mm"

theorem supadd
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
  let va: setvar a
  assume supadd.a1: |- ( ph -> A C_ RR )
  assume supadd.a2: |- ( ph -> A =/= (/) )
  assume supadd.a3: |- ( ph -> E. x e. RR A. y e. A y <_ x )
  assume supadd.b1: |- ( ph -> B C_ RR )
  assume supadd.b2: |- ( ph -> B =/= (/) )
  assume supadd.b3: |- ( ph -> E. x e. RR A. y e. B y <_ x )
  assume supadd.c: |- C = { z | E. v e. A E. b e. B z = ( v + b ) }

  disjoint x y
  disjoint x z
  disjoint b x
  disjoint v x
  disjoint A x
  disjoint y z
  disjoint b y
  disjoint v y
  disjoint A y
  disjoint b z
  disjoint v z
  disjoint A z
  disjoint b v
  disjoint A b
  disjoint A v
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B b
  disjoint B v
  disjoint C x
  disjoint ph z
  disjoint b ph
  disjoint ph v
  disjoint w x
  disjoint a x
  disjoint w y
  disjoint a y
  disjoint w z
  disjoint a z
  disjoint b w
  disjoint a b
  disjoint v w
  disjoint a v
  disjoint a w
  disjoint A w
  disjoint A a
  disjoint B w
  disjoint B a
  disjoint C w
  disjoint C a
  disjoint ph w
  disjoint a ph
  assert |- ( ph -> ( sup ( A , RR , < ) + sup ( B , RR , < ) ) = sup ( C , RR , < ) )

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
    caddc
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
    caddc
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
    @5
    @6
    @1
    caddc
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
    @11
    wph
    vx
    vy
    vz
    va
    cA
    @1
    @15
    supadd.a1
    supadd.a2
    supadd.a3
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
    #
    vy
    cB
    wral
    vx
    cr
    wrex
    #
    @1
    cr
    wcel
    #
    supadd.b1
    supadd.b2
    supadd.b3
    vx
    vy
    cB
    suprcl
    syl3anc
    #
    @15
    eqid
    supaddc
    wph
    cr
    @15
    @10
    clt
    wph
    @14
    @9
    vz
    wph
    @13
    @8
    va
    cA
    wph
    @6
    cA
    wcel
    #
    wa
    #
    @12
    @7
    @5
    @24
    @6
    @1
    @24
    @6
    wph
    cA
    cr
    @6
    supadd.a1
    sselda
    #
    recnd
    @24
    @1
    wph
    @21
    @23
    @22
    adantr
    #
    recnd
    addcomd
    eqeq2d
    rexbidva
    abbidv
    supeq1d
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
    @29
    vw
    @10
    @28
    @10
    wcel
    @28
    @7
    wceq
    #
    va
    cA
    wrex
    #
    wph
    @29
    @9
    @32
    vz
    @28
    vw
    vex
    #
    vz
    vw
    weq
    #
    @8
    @31
    va
    cA
    @5
    @28
    @7
    eqeq1
    rexbidv
    elab
    wph
    @31
    @29
    va
    cA
    @24
    @29
    @31
    @7
    @3
    cle
    wbr
    @24
    @7
    @5
    @6
    vb
    cv
    #
    caddc
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
    @24
    @7
    @5
    @35
    @6
    caddc
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
    @40
    @24
    vx
    vy
    vz
    vb
    cB
    @6
    @44
    wph
    @16
    @23
    supadd.b1
    adantr
    wph
    @17
    @23
    supadd.b2
    adantr
    wph
    @20
    @23
    supadd.b3
    adantr
    @25
    @44
    eqid
    supaddc
    @24
    cr
    @44
    @39
    clt
    @24
    @43
    @38
    vz
    @24
    @42
    @37
    vb
    cB
    @24
    @35
    cB
    wcel
    #
    wa
    #
    @41
    @36
    @5
    @46
    @35
    @6
    @46
    @35
    wph
    @45
    @35
    cr
    wcel
    #
    @23
    wph
    cB
    cr
    @35
    supadd.b1
    sselda
    #
    adantlr
    #
    recnd
    @46
    @6
    @24
    @6
    cr
    wcel
    #
    @45
    @25
    adantr
    #
    recnd
    addcomd
    eqeq2d
    rexbidva
    abbidv
    supeq1d
    eqtrd
    @24
    @40
    @3
    cle
    wbr
    #
    @29
    vw
    @39
    wral
    #
    @24
    @29
    vw
    @39
    @28
    @39
    wcel
    @28
    @36
    wceq
    #
    vb
    cB
    wrex
    #
    @24
    @29
    @38
    @55
    vz
    @28
    @33
    @34
    @37
    @54
    vb
    cB
    @5
    @28
    @36
    eqeq1
    #
    rexbidv
    elab
    @23
    @55
    @28
    cC
    wcel
    #
    wph
    @29
    @23
    @55
    @57
    @23
    @55
    wa
    @55
    va
    cA
    wrex
    #
    @57
    @55
    va
    cA
    rspe
    @5
    vv
    cv
    #
    @35
    caddc
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
    @58
    vz
    @28
    cC
    @33
    @63
    @38
    va
    cA
    wrex
    @34
    @58
    @62
    @38
    vv
    va
    cA
    vv
    va
    weq
    #
    @61
    @37
    vb
    cB
    @64
    @60
    @36
    @5
    @59
    @6
    @35
    caddc
    oveq1
    eqeq2d
    rexbidv
    cbvrexv
    @34
    @37
    @54
    va
    vb
    cA
    cB
    @56
    2rexbidv
    syl5bb
    supadd.c
    elab2
    #
    sylibr
    ex
    wph
    cC
    cr
    wss
    #
    cC
    c0
    wne
    #
    @28
    @18
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
    @57
    @29
    wi
    wph
    vw
    cC
    cr
    @57
    @58
    wph
    @28
    cr
    wcel
    #
    @65
    wph
    @54
    @71
    va
    vb
    cA
    cB
    wph
    @23
    @45
    wa
    #
    @36
    cr
    wcel
    #
    @54
    @71
    wi
    wph
    @72
    @50
    @47
    wa
    @73
    wph
    @23
    @50
    @45
    @47
    wph
    cA
    cr
    @6
    supadd.a1
    sseld
    wph
    cB
    cr
    @35
    supadd.b1
    sseld
    anim12d
    @6
    @35
    readdcl
    syl6
    @36
    cr
    @28
    eleq1a
    syl6
    rexlimdvv
    syl5bi
    ssrdv
    #
    wph
    @58
    vw
    wex
    #
    @67
    wph
    @55
    vw
    wex
    #
    va
    cA
    wrex
    #
    @75
    wph
    cA
    c0
    wne
    #
    @76
    va
    cA
    wral
    @77
    supadd.a2
    wph
    @76
    va
    cA
    wph
    @54
    vw
    wex
    #
    vb
    cB
    wrex
    #
    @76
    wph
    @17
    @79
    vb
    cB
    wral
    @80
    supadd.b2
    @79
    vb
    cB
    vw
    @36
    @6
    @35
    caddc
    ovex
    #
    isseti
    rgenw
    @79
    vb
    cB
    r19.2z
    sylancl
    @54
    vb
    vw
    cB
    rexcom4
    sylib
    ralrimivw
    @76
    va
    cA
    r19.2z
    syl2anc
    @55
    va
    vw
    cA
    rexcom4
    sylib
    @67
    @57
    vw
    wex
    @75
    vw
    cC
    n0
    @57
    @58
    vw
    @65
    exbii
    bitri
    sylibr
    #
    wph
    @2
    cr
    wcel
    #
    @28
    @2
    cle
    wbr
    #
    vw
    cC
    wral
    #
    @70
    wph
    @0
    @1
    wph
    cA
    cr
    wss
    #
    @78
    @19
    vy
    cA
    wral
    vx
    cr
    wrex
    #
    @0
    cr
    wcel
    #
    supadd.a1
    supadd.a2
    supadd.a3
    vx
    vy
    cA
    suprcl
    syl3anc
    #
    @22
    readdcld
    #
    wph
    @84
    vw
    cC
    @57
    @58
    wph
    @84
    @65
    wph
    @54
    @84
    va
    vb
    cA
    cB
    wph
    @72
    @36
    @2
    cle
    wbr
    #
    @54
    @84
    wi
    wph
    @72
    @91
    wph
    @72
    wa
    @6
    @35
    @0
    @1
    wph
    @23
    @50
    @45
    @25
    adantrr
    wph
    @45
    @47
    @23
    @48
    adantrl
    wph
    @88
    @72
    @89
    adantr
    wph
    @21
    @72
    @22
    adantr
    wph
    @23
    @6
    @0
    cle
    wbr
    #
    @45
    wph
    @86
    @78
    @87
    w3a
    @23
    @92
    wph
    @86
    @78
    @87
    supadd.a1
    supadd.a2
    supadd.a3
    3jca
    vx
    vy
    cA
    @6
    suprub
    sylan
    adantrr
    wph
    @45
    @35
    @1
    cle
    wbr
    #
    @23
    wph
    @16
    @17
    @20
    w3a
    @45
    @93
    wph
    @16
    @17
    @20
    supadd.b1
    supadd.b2
    supadd.b3
    3jca
    vx
    vy
    cB
    @35
    suprub
    sylan
    adantrl
    le2addd
    ex
    @54
    @84
    @91
    @28
    @36
    @2
    cle
    breq1
    biimprcd
    syl6
    rexlimdvv
    syl5bi
    ralrimiv
    #
    @69
    @85
    vx
    @2
    cr
    @18
    @2
    wceq
    @68
    @84
    vw
    cC
    @18
    @2
    @28
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    @66
    @67
    @70
    w3a
    @57
    @29
    vx
    vw
    cC
    @28
    suprub
    ex
    syl3anc
    sylan9r
    syl5bi
    ralrimiv
    #
    @24
    @39
    cr
    wss
    @39
    c0
    wne
    #
    @68
    vw
    @39
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
    @52
    @53
    wb
    @24
    @38
    vz
    cr
    @24
    @37
    @5
    cr
    wcel
    #
    vb
    cB
    @46
    @73
    @37
    @101
    wi
    @46
    @6
    @35
    @51
    @49
    readdcld
    @36
    cr
    @5
    eleq1a
    syl
    rexlimdva
    abssdv
    wph
    @97
    @23
    wph
    @38
    vz
    wex
    #
    @97
    wph
    @37
    vz
    wex
    #
    vb
    cB
    wrex
    #
    @102
    wph
    @17
    @103
    vb
    cB
    wral
    @104
    supadd.b2
    @103
    vb
    cB
    vz
    @36
    @81
    isseti
    rgenw
    @103
    vb
    cB
    r19.2z
    sylancl
    @37
    vb
    vz
    cB
    rexcom4
    sylib
    @38
    vz
    abn0
    sylibr
    adantr
    @24
    @100
    @53
    @99
    wph
    @100
    @23
    wph
    @66
    @67
    @70
    @100
    @74
    @82
    @95
    vx
    vw
    cC
    suprcl
    syl3anc
    #
    adantr
    #
    @96
    @98
    @53
    vx
    @3
    cr
    @18
    @3
    wceq
    #
    @68
    @29
    vw
    @39
    @18
    @3
    @28
    cle
    breq2
    #
    ralbidv
    rspcev
    syl2anc
    @106
    vx
    vw
    vw
    @39
    @3
    suprleub
    syl31anc
    mpbird
    eqbrtrd
    @28
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
    @68
    vw
    @10
    wral
    #
    vx
    cr
    wrex
    #
    @100
    @27
    @30
    wb
    wph
    @9
    vz
    cr
    wph
    @8
    @101
    va
    cA
    @24
    @7
    cr
    wcel
    @8
    @101
    wi
    @24
    @1
    @6
    @26
    @25
    readdcld
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
    @110
    wph
    @8
    vz
    wex
    #
    va
    cA
    wrex
    #
    @113
    wph
    @78
    @114
    va
    cA
    wral
    @115
    supadd.a2
    @114
    va
    cA
    vz
    @7
    @1
    @6
    caddc
    ovex
    isseti
    rgenw
    @114
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
    @100
    @30
    @112
    @105
    @109
    @111
    @30
    vx
    @3
    cr
    @107
    @68
    @29
    vw
    @10
    @108
    ralbidv
    rspcev
    syl2anc
    @105
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
    @85
    @94
    wph
    @66
    @67
    @70
    @83
    @4
    @85
    wb
    @74
    @82
    @95
    @90
    vx
    vw
    vw
    cC
    @2
    suprleub
    syl31anc
    mpbird
    wph
    @2
    @3
    @90
    @105
    letri3d
    mpbir2and
end
