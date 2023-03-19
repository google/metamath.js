include "cv.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wcel.mm"
include "wceq.mm"
include "wrex.mm"
include "vex.mm"
include "weq.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "cbvrexv.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "syl5bb.mm"
include "elab2.mm"
include "wa.mm"
include "wi.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cc0.mm"
include "w3a.mm"
include "simp2bi.mm"
include "simp1d.mm"
include "sselda.mm"
include "adantrr.mm"
include "suprcl.mm"
include "syl.mm"
include "adantr.mm"
include "simp3bi.mm"
include "adantrl.mm"
include "simp1l.mm"
include "sylbi.mm"
include "breq2.mm"
include "rspccv.mm"
include "imp.mm"
include "simp1r.mm"
include "suprub.mm"
include "sylan.mm"
include "lemul12ad.mm"
include "ex.mm"
include "breq1.mm"
include "biimprcd.mm"
include "syl6.mm"
include "rexlimdvv.mm"
include "syl5bi.mm"
include "ralrimiv.mm"

theorem supmullem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let vb: setvar b
  let va: setvar a
  assume supmul.1: |- C = { z | E. v e. A E. b e. B z = ( v x. b ) }
  assume supmul.2: |- ( ph <-> ( ( A. x e. A 0 <_ x /\ A. x e. B 0 <_ x ) /\ ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A y <_ x ) /\ ( B C_ RR /\ B =/= (/) /\ E. x e. RR A. y e. B y <_ x ) ) )

  disjoint A b
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint A w
  disjoint A z
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b w
  disjoint b z
  disjoint v x
  disjoint v y
  disjoint v w
  disjoint v z
  disjoint x y
  disjoint w x
  disjoint x z
  disjoint w y
  disjoint y z
  disjoint w z
  disjoint B b
  disjoint B v
  disjoint B x
  disjoint B y
  disjoint B w
  disjoint B z
  disjoint C x
  disjoint C w
  disjoint b ph
  disjoint ph w
  disjoint ph z
  disjoint A a
  disjoint a b
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a w
  disjoint a z
  disjoint B a
  disjoint C a
  disjoint a ph
  assert |- ( ph -> A. w e. C w <_ ( sup ( A , RR , < ) x. sup ( B , RR , < ) ) )

  proof
    wph
    vw
    cv
    #
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
    cle
    wbr
    #
    vw
    cC
    @0
    cC
    wcel
    @0
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
    cB
    wrex
    va
    cA
    wrex
    #
    wph
    @4
    vz
    cv
    #
    vv
    cv
    #
    @6
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
    @9
    vz
    @0
    cC
    vw
    vex
    @15
    @10
    @7
    wceq
    #
    vb
    cB
    wrex
    #
    va
    cA
    wrex
    vz
    vw
    weq
    #
    @9
    @14
    @17
    vv
    va
    cA
    vv
    va
    weq
    #
    @13
    @16
    vb
    cB
    @19
    @12
    @7
    @10
    @11
    @5
    @6
    cmul
    oveq1
    eqeq2d
    rexbidv
    cbvrexv
    @18
    @16
    @8
    va
    vb
    cA
    cB
    @10
    @0
    @7
    eqeq1
    2rexbidv
    syl5bb
    supmul.1
    elab2
    wph
    @8
    @4
    va
    vb
    cA
    cB
    wph
    @5
    cA
    wcel
    #
    @6
    cB
    wcel
    #
    wa
    #
    @7
    @3
    cle
    wbr
    #
    @8
    @4
    wi
    wph
    @22
    @23
    wph
    @22
    wa
    @5
    @1
    @6
    @2
    wph
    @20
    @5
    cr
    wcel
    @21
    wph
    cA
    cr
    @5
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
    wph
    cc0
    @26
    cle
    wbr
    #
    vx
    cA
    wral
    #
    @29
    vx
    cB
    wral
    #
    wa
    #
    @24
    @25
    @28
    w3a
    #
    cB
    cr
    wss
    #
    cB
    c0
    wne
    #
    @27
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
    simp1d
    sselda
    adantrr
    wph
    @1
    cr
    wcel
    #
    @22
    wph
    @33
    @39
    @38
    vx
    vy
    cA
    suprcl
    syl
    adantr
    wph
    @21
    @6
    cr
    wcel
    @20
    wph
    cB
    cr
    @6
    wph
    @34
    @35
    @36
    wph
    @32
    @33
    @37
    supmul.2
    simp3bi
    #
    simp1d
    sselda
    adantrl
    wph
    @2
    cr
    wcel
    #
    @22
    wph
    @37
    @41
    @40
    vx
    vy
    cB
    suprcl
    syl
    adantr
    wph
    @20
    cc0
    @5
    cle
    wbr
    #
    @21
    wph
    @20
    @42
    wph
    @30
    @20
    @42
    wi
    wph
    @32
    @33
    @37
    w3a
    #
    @30
    supmul.2
    @30
    @31
    @33
    @37
    simp1l
    sylbi
    @29
    @42
    vx
    @5
    cA
    @26
    @5
    cc0
    cle
    breq2
    rspccv
    syl
    imp
    adantrr
    wph
    @21
    cc0
    @6
    cle
    wbr
    #
    @20
    wph
    @21
    @44
    wph
    @31
    @21
    @44
    wi
    wph
    @43
    @31
    supmul.2
    @30
    @31
    @33
    @37
    simp1r
    sylbi
    @29
    @44
    vx
    @6
    cB
    @26
    @6
    cc0
    cle
    breq2
    rspccv
    syl
    imp
    adantrl
    wph
    @20
    @5
    @1
    cle
    wbr
    #
    @21
    wph
    @33
    @20
    @45
    @38
    vx
    vy
    cA
    @5
    suprub
    sylan
    adantrr
    wph
    @21
    @6
    @2
    cle
    wbr
    #
    @20
    wph
    @37
    @21
    @46
    @40
    vx
    vy
    cB
    @6
    suprub
    sylan
    adantrl
    lemul12ad
    ex
    @8
    @4
    @23
    @0
    @7
    @3
    cle
    breq1
    biimprcd
    syl6
    rexlimdvv
    syl5bi
    ralrimiv
end
