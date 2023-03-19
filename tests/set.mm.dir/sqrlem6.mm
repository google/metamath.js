include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "wceq.mm"
include "sqrlem5.mm"
include "simprd.mm"
include "cmul.mm"
include "vex.mm"
include "weq.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "elab2.mm"
include "wi.mm"
include "wb.mm"
include "oveq1.mm"
include "breq1d.mm"
include "elrab2.mm"
include "simplbi.mm"
include "cc0.mm"
include "rpre.mm"
include "adantr.mm"
include "adantl.mm"
include "rpgt0.mm"
include "lemul1.mm"
include "syl112anc.mm"
include "syl2an.mm"
include "rpcnd.mm"
include "sqvald.mm"
include "breq2d.mm"
include "bitr4d.mm"
include "simprbi.mm"
include "ad2antll.mm"
include "rpred.mm"
include "remulcl.mm"
include "resqcld.mm"
include "ad2antrr.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "sylbid.mm"
include "lemul2.mm"
include "ad2antrl.mm"
include "wo.mm"
include "sqrlem3.mm"
include "simp1d.mm"
include "sseld.mm"
include "anim12d.mm"
include "imp.mm"
include "letric.mm"
include "syl.mm"
include "mpjaod.mm"
include "ex.mm"
include "breq1.mm"
include "biimprcd.mm"
include "syl6.mm"
include "rexlimdvv.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "simpld.mm"
include "suprleub.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "eqbrtrd.mm"

theorem sqrlem6
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  assume sqrlem1.1: |- S = { x e. RR+ | ( x ^ 2 ) <_ A }
  assume sqrlem1.2: |- B = sup ( S , RR , < )
  assume sqrlem5.3: |- T = { y | E. a e. S E. b e. S y = ( a x. b ) }

  disjoint a b
  disjoint a y
  disjoint S a
  disjoint b y
  disjoint S b
  disjoint S y
  disjoint a x
  disjoint A a
  disjoint b x
  disjoint A b
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint a u
  disjoint a v
  disjoint a z
  disjoint b u
  disjoint b v
  disjoint b z
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint S u
  disjoint v y
  disjoint v z
  disjoint S v
  disjoint y z
  disjoint S z
  disjoint v x
  disjoint A v
  disjoint x z
  disjoint A z
  disjoint B v
  disjoint B z
  disjoint T u
  disjoint T v
  assert |- ( ( A e. RR+ /\ A <_ 1 ) -> ( B ^ 2 ) <_ A )

  proof
    cA
    crp
    wcel
    #
    cA
    c1
    cle
    wbr
    #
    wa
    #
    cB
    c2
    cexp
    co
    #
    cT
    cr
    clt
    csup
    #
    cA
    cle
    @2
    cT
    cr
    wss
    cT
    c0
    wne
    vu
    cv
    vv
    cv
    #
    cle
    wbr
    vu
    cT
    wral
    vv
    cr
    wrex
    w3a
    #
    @3
    @4
    wceq
    #
    vx
    vy
    vv
    vu
    cA
    cB
    cS
    cT
    va
    vb
    sqrlem1.1
    sqrlem1.2
    sqrlem5.3
    sqrlem5
    #
    simprd
    @2
    @4
    cA
    cle
    wbr
    #
    @5
    cA
    cle
    wbr
    #
    vv
    cT
    wral
    #
    @2
    @10
    vv
    cT
    @5
    cT
    wcel
    @5
    va
    cv
    #
    vb
    cv
    #
    cmul
    co
    #
    wceq
    #
    vb
    cS
    wrex
    va
    cS
    wrex
    #
    @2
    @10
    vy
    cv
    #
    @14
    wceq
    #
    vb
    cS
    wrex
    va
    cS
    wrex
    @16
    vy
    @5
    cT
    vv
    vex
    vy
    vv
    weq
    @18
    @15
    va
    vb
    cS
    cS
    @17
    @5
    @14
    eqeq1
    2rexbidv
    sqrlem5.3
    elab2
    @2
    @15
    @10
    va
    vb
    cS
    cS
    @2
    @12
    cS
    wcel
    #
    @13
    cS
    wcel
    #
    wa
    #
    @14
    cA
    cle
    wbr
    #
    @15
    @10
    wi
    @2
    @21
    @22
    @2
    @21
    wa
    #
    @12
    @13
    cle
    wbr
    #
    @22
    @13
    @12
    cle
    wbr
    #
    @23
    @24
    @14
    @13
    c2
    cexp
    co
    #
    cle
    wbr
    #
    @22
    @21
    @24
    @27
    wb
    @2
    @21
    @24
    @14
    @13
    @13
    cmul
    co
    #
    cle
    wbr
    #
    @27
    @19
    @12
    crp
    wcel
    #
    @13
    crp
    wcel
    #
    @24
    @29
    wb
    #
    @20
    @19
    @30
    @12
    c2
    cexp
    co
    #
    cA
    cle
    wbr
    #
    vx
    cv
    #
    c2
    cexp
    co
    #
    cA
    cle
    wbr
    #
    @34
    vx
    @12
    crp
    cS
    vx
    va
    weq
    @36
    @33
    cA
    cle
    @35
    @12
    c2
    cexp
    oveq1
    breq1d
    sqrlem1.1
    elrab2
    #
    simplbi
    #
    @20
    @31
    @26
    cA
    cle
    wbr
    #
    @37
    @40
    vx
    @13
    crp
    cS
    vx
    vb
    weq
    @36
    @26
    cA
    cle
    @35
    @13
    c2
    cexp
    oveq1
    breq1d
    sqrlem1.1
    elrab2
    #
    simplbi
    #
    @30
    @31
    wa
    #
    @12
    cr
    wcel
    #
    @13
    cr
    wcel
    #
    @45
    cc0
    @13
    clt
    wbr
    #
    @32
    @30
    @44
    @31
    @12
    rpre
    adantr
    #
    @31
    @45
    @30
    @13
    rpre
    adantl
    #
    @48
    @31
    @46
    @30
    @13
    rpgt0
    adantl
    @12
    @13
    @13
    lemul1
    syl112anc
    syl2an
    @20
    @27
    @29
    wb
    @19
    @20
    @26
    @28
    @14
    cle
    @20
    @13
    @20
    @13
    @42
    rpcnd
    sqvald
    breq2d
    adantl
    bitr4d
    adantl
    @23
    @27
    @40
    @22
    @20
    @40
    @2
    @19
    @20
    @31
    @40
    @41
    simprbi
    ad2antll
    @23
    @14
    cr
    wcel
    #
    @26
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    @27
    @40
    wa
    @22
    wi
    @21
    @49
    @2
    @19
    @44
    @45
    @49
    @20
    @19
    @12
    @39
    rpred
    #
    @20
    @13
    @42
    rpred
    #
    @12
    @13
    remulcl
    syl2an
    adantl
    #
    @20
    @50
    @2
    @19
    @20
    @13
    @53
    resqcld
    ad2antll
    @0
    @51
    @1
    @21
    cA
    rpre
    #
    ad2antrr
    #
    @14
    @26
    cA
    letr
    syl3anc
    mpan2d
    sylbid
    @23
    @25
    @14
    @33
    cle
    wbr
    #
    @22
    @21
    @25
    @57
    wb
    @2
    @21
    @25
    @14
    @12
    @12
    cmul
    co
    #
    cle
    wbr
    #
    @57
    @19
    @30
    @31
    @25
    @59
    wb
    #
    @20
    @39
    @42
    @43
    @45
    @44
    @44
    cc0
    @12
    clt
    wbr
    #
    @60
    @48
    @47
    @47
    @30
    @61
    @31
    @12
    rpgt0
    adantr
    @13
    @12
    @12
    lemul2
    syl112anc
    syl2an
    @19
    @57
    @59
    wb
    @20
    @19
    @33
    @58
    @14
    cle
    @19
    @12
    @19
    @12
    @39
    rpcnd
    sqvald
    breq2d
    adantr
    bitr4d
    adantl
    @23
    @57
    @34
    @22
    @19
    @34
    @2
    @20
    @19
    @30
    @34
    @38
    simprbi
    ad2antrl
    @23
    @49
    @33
    cr
    wcel
    #
    @51
    @57
    @34
    wa
    @22
    wi
    @54
    @19
    @62
    @2
    @20
    @19
    @12
    @52
    resqcld
    ad2antrl
    @56
    @14
    @33
    cA
    letr
    syl3anc
    mpan2d
    sylbid
    @23
    @44
    @45
    wa
    #
    @24
    @25
    wo
    @2
    @21
    @63
    @2
    @19
    @44
    @20
    @45
    @2
    cS
    cr
    @12
    @2
    cS
    cr
    wss
    cS
    c0
    wne
    @5
    @17
    cle
    wbr
    vv
    cS
    wral
    vy
    cr
    wrex
    vx
    vv
    vy
    cA
    cB
    cS
    sqrlem1.1
    sqrlem1.2
    sqrlem3
    simp1d
    #
    sseld
    @2
    cS
    cr
    @13
    @64
    sseld
    anim12d
    imp
    @12
    @13
    letric
    syl
    mpjaod
    ex
    @15
    @10
    @22
    @5
    @14
    cA
    cle
    breq1
    biimprcd
    syl6
    rexlimdvv
    syl5bi
    ralrimiv
    @2
    @6
    @51
    @9
    @11
    wb
    @2
    @6
    @7
    @8
    simpld
    @0
    @51
    @1
    @55
    adantr
    vv
    vu
    vv
    cT
    cA
    suprleub
    syl2anc
    mpbird
    eqbrtrd
end
