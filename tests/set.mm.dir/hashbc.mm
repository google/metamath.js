include "cfn.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "cbc.mm"
include "co.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "cz.mm"
include "wral.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "pweq.mm"
include "rabeq.mm"
include "syl.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "cc0.mm"
include "cfz.mm"
include "c1.mm"
include "hash0.mm"
include "a1i.mm"
include "elfz1eq.mm"
include "oveq12d.mm"
include "cn0.mm"
include "0nn0.mm"
include "bcn0.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "pw0.mm"
include "eqcomd.mm"
include "raleqi.mm"
include "0ex.mm"
include "eqeq1d.mm"
include "ralsn.mm"
include "bitri.mm"
include "sylibr.mm"
include "rabid2.mm"
include "syl5reqr.mm"
include "cvv.mm"
include "hashsng.mm"
include "eqtr4d.mm"
include "adantl.mm"
include "wn.mm"
include "wa.mm"
include "oveq1i.mm"
include "bcval3.mm"
include "mp3an1.mm"
include "id.mm"
include "0z.mm"
include "elfz3.mm"
include "syl6eqelr.mm"
include "con3i.mm"
include "notbid.mm"
include "rabeq0.mm"
include "syl5eq.mm"
include "pm2.61dan.mm"
include "rgen.mm"
include "oveq2.mm"
include "eqeq2.mm"
include "rabbidv.mm"
include "cbvrabv.mm"
include "cbvralv.mm"
include "simpll.mm"
include "simplr.mm"
include "simprr.mm"
include "fveq2i.mm"
include "eqeq2i.mm"
include "ralbii.mm"
include "simprl.mm"
include "hashbclem.mm"
include "expr.mm"
include "ralrimdva.mm"
include "syl5bi.mm"
include "findcard2s.mm"
include "rspccva.mm"
include "sylan.mm"

theorem hashbc
  let vx: setvar x
  let cA: class A
  let cK: class K
  let vj: setvar j
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph

  disjoint A x
  disjoint K x
  disjoint j k
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint K j
  disjoint K k
  disjoint K u
  disjoint K v
  disjoint ph u
  disjoint ph v
  disjoint ph x
  assert |- ( ( A e. Fin /\ K e. ZZ ) -> ( ( # ` A ) _C K ) = ( # ` { x e. ~P A | ( # ` x ) = K } ) )

  proof
    cA
    cfn
    wcel
    cA
    chash
    cfv
    #
    vk
    cv
    #
    cbc
    co
    #
    vx
    cv
    #
    chash
    cfv
    #
    @1
    wceq
    #
    vx
    cA
    cpw
    #
    crab
    #
    chash
    cfv
    #
    wceq
    #
    vk
    cz
    wral
    #
    cK
    cz
    wcel
    @0
    cK
    cbc
    co
    #
    @4
    cK
    wceq
    #
    vx
    @6
    crab
    #
    chash
    cfv
    #
    wceq
    #
    vw
    cv
    #
    chash
    cfv
    #
    @1
    cbc
    co
    #
    @5
    vx
    @16
    cpw
    #
    crab
    #
    chash
    cfv
    #
    wceq
    #
    vk
    cz
    wral
    c0
    chash
    cfv
    #
    @1
    cbc
    co
    #
    @5
    vx
    c0
    cpw
    #
    crab
    #
    chash
    cfv
    #
    wceq
    #
    vk
    cz
    wral
    vy
    cv
    #
    chash
    cfv
    #
    @1
    cbc
    co
    #
    @5
    vx
    @29
    cpw
    #
    crab
    #
    chash
    cfv
    #
    wceq
    #
    vk
    cz
    wral
    #
    @29
    vz
    cv
    #
    csn
    cun
    #
    chash
    cfv
    #
    @1
    cbc
    co
    #
    @5
    vx
    @38
    cpw
    #
    crab
    #
    chash
    cfv
    #
    wceq
    #
    vk
    cz
    wral
    #
    @10
    vw
    vy
    vz
    cA
    @16
    c0
    wceq
    #
    @22
    @28
    vk
    cz
    @46
    @18
    @24
    @21
    @27
    @46
    @17
    @23
    @1
    cbc
    @16
    c0
    chash
    fveq2
    oveq1d
    @46
    @20
    @26
    chash
    @46
    @19
    @25
    wceq
    @20
    @26
    wceq
    @16
    c0
    pweq
    @5
    vx
    @19
    @25
    rabeq
    syl
    fveq2d
    eqeq12d
    ralbidv
    @16
    @29
    wceq
    #
    @22
    @35
    vk
    cz
    @47
    @18
    @31
    @21
    @34
    @47
    @17
    @30
    @1
    cbc
    @16
    @29
    chash
    fveq2
    oveq1d
    @47
    @20
    @33
    chash
    @47
    @19
    @32
    wceq
    @20
    @33
    wceq
    @16
    @29
    pweq
    @5
    vx
    @19
    @32
    rabeq
    syl
    fveq2d
    eqeq12d
    ralbidv
    @16
    @38
    wceq
    #
    @22
    @44
    vk
    cz
    @48
    @18
    @40
    @21
    @43
    @48
    @17
    @39
    @1
    cbc
    @16
    @38
    chash
    fveq2
    oveq1d
    @48
    @20
    @42
    chash
    @48
    @19
    @41
    wceq
    @20
    @42
    wceq
    @16
    @38
    pweq
    @5
    vx
    @19
    @41
    rabeq
    syl
    fveq2d
    eqeq12d
    ralbidv
    @16
    cA
    wceq
    #
    @22
    @9
    vk
    cz
    @49
    @18
    @2
    @21
    @8
    @49
    @17
    @0
    @1
    cbc
    @16
    cA
    chash
    fveq2
    oveq1d
    @49
    @20
    @7
    chash
    @49
    @19
    @6
    wceq
    @20
    @7
    wceq
    @16
    cA
    pweq
    @5
    vx
    @19
    @6
    rabeq
    syl
    fveq2d
    eqeq12d
    ralbidv
    @28
    vk
    cz
    @1
    cz
    wcel
    #
    @1
    cc0
    cc0
    cfz
    co
    #
    wcel
    #
    @28
    @52
    @28
    @50
    @52
    @24
    c1
    @27
    @52
    @24
    cc0
    cc0
    cbc
    co
    #
    c1
    @52
    @23
    cc0
    @1
    cc0
    cbc
    @23
    cc0
    wceq
    @52
    hash0
    a1i
    @1
    cc0
    elfz1eq
    #
    oveq12d
    cc0
    cn0
    wcel
    #
    @53
    c1
    wceq
    0nn0
    cc0
    bcn0
    ax-mp
    syl6eq
    @52
    @27
    c0
    csn
    #
    chash
    cfv
    #
    c1
    @52
    @26
    @56
    chash
    @52
    @56
    @25
    @26
    pw0
    @52
    @5
    vx
    @25
    wral
    #
    @25
    @26
    wceq
    @52
    cc0
    @1
    wceq
    #
    @58
    @52
    @1
    cc0
    @54
    eqcomd
    @58
    @5
    vx
    @56
    wral
    @59
    @5
    vx
    @25
    @56
    pw0
    raleqi
    @5
    @59
    vx
    c0
    0ex
    @3
    c0
    wceq
    #
    @4
    cc0
    @1
    @60
    @4
    @23
    cc0
    @3
    c0
    chash
    fveq2
    hash0
    syl6eq
    eqeq1d
    #
    ralsn
    bitri
    sylibr
    @5
    vx
    @25
    rabid2
    sylibr
    syl5reqr
    fveq2d
    c0
    cvv
    wcel
    @57
    c1
    wceq
    0ex
    c0
    cvv
    hashsng
    ax-mp
    syl6eq
    eqtr4d
    adantl
    @50
    @52
    wn
    #
    wa
    #
    @24
    cc0
    @1
    cbc
    co
    #
    @27
    @23
    cc0
    @1
    cbc
    hash0
    oveq1i
    @63
    @64
    cc0
    @27
    @55
    @50
    @62
    @64
    cc0
    wceq
    0nn0
    @1
    cc0
    bcval3
    mp3an1
    @63
    @27
    @23
    cc0
    @63
    @26
    c0
    chash
    @63
    @5
    wn
    #
    vx
    @25
    wral
    #
    @26
    c0
    wceq
    @63
    @59
    wn
    #
    @66
    @62
    @67
    @50
    @59
    @52
    @59
    @1
    cc0
    @51
    @59
    id
    cc0
    cz
    wcel
    cc0
    @51
    wcel
    0z
    cc0
    elfz3
    ax-mp
    syl6eqelr
    con3i
    adantl
    @66
    @65
    vx
    @56
    wral
    @67
    @65
    vx
    @25
    @56
    pw0
    raleqi
    @65
    @67
    vx
    c0
    0ex
    @60
    @5
    @59
    @61
    notbid
    ralsn
    bitri
    sylibr
    @5
    vx
    @25
    rabeq0
    sylibr
    fveq2d
    hash0
    syl6eq
    eqtr4d
    syl5eq
    pm2.61dan
    rgen
    @36
    @30
    vj
    cv
    #
    cbc
    co
    #
    @37
    chash
    cfv
    #
    @68
    wceq
    #
    vz
    @32
    crab
    #
    chash
    cfv
    #
    wceq
    #
    vj
    cz
    wral
    #
    @29
    cfn
    wcel
    #
    @37
    @29
    wcel
    wn
    #
    wa
    #
    @45
    @35
    @74
    vk
    vj
    cz
    @1
    @68
    wceq
    #
    @31
    @69
    @34
    @73
    @1
    @68
    @30
    cbc
    oveq2
    @79
    @33
    @72
    chash
    @79
    @33
    @4
    @68
    wceq
    #
    vx
    @32
    crab
    #
    @72
    @79
    @5
    @80
    vx
    @32
    @1
    @68
    @4
    eqeq2
    rabbidv
    @80
    @71
    vx
    vz
    @32
    @3
    @37
    wceq
    @4
    @70
    @68
    @3
    @37
    chash
    fveq2
    eqeq1d
    cbvrabv
    #
    syl6eq
    fveq2d
    eqeq12d
    cbvralv
    @78
    @75
    @44
    vk
    cz
    @78
    @50
    @75
    @44
    @78
    @50
    @75
    wa
    #
    wa
    #
    vx
    vz
    @29
    vj
    @1
    @76
    @77
    @83
    simpll
    @76
    @77
    @83
    simplr
    @84
    @75
    @69
    @81
    chash
    cfv
    #
    wceq
    #
    vj
    cz
    wral
    @78
    @50
    @75
    simprr
    @86
    @74
    vj
    cz
    @85
    @73
    @69
    @81
    @72
    chash
    @82
    fveq2i
    eqeq2i
    ralbii
    sylibr
    @78
    @50
    @75
    simprl
    hashbclem
    expr
    ralrimdva
    syl5bi
    findcard2s
    @9
    @15
    vk
    cK
    cz
    @1
    cK
    wceq
    #
    @2
    @11
    @8
    @14
    @1
    cK
    @0
    cbc
    oveq2
    @87
    @7
    @13
    chash
    @87
    @5
    @12
    vx
    @6
    @1
    cK
    @4
    eqeq2
    rabbidv
    fveq2d
    eqeq12d
    rspccva
    sylan
end
