include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "vex.mm"
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
include "cc0.mm"
include "w3a.mm"
include "simp2bi.mm"
include "simp1d.mm"
include "sseld.mm"
include "simp3bi.mm"
include "anim12d.mm"
include "remulcl.mm"
include "syl6.mm"
include "eleq1a.mm"
include "rexlimdvv.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "wex.mm"
include "simp2d.mm"
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
include "sylibr.mm"
include "clt.mm"
include "csup.mm"
include "suprcl.mm"
include "syl.mm"
include "remulcld.mm"
include "supmullem1.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "3jca.mm"

theorem supmullem2
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
  assert |- ( ph -> ( C C_ RR /\ C =/= (/) /\ E. x e. RR A. w e. C w <_ x ) )

  proof
    wph
    cC
    cr
    wss
    cC
    c0
    wne
    #
    vw
    cv
    #
    vx
    cv
    #
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
    wph
    vw
    cC
    cr
    @1
    cC
    wcel
    #
    @1
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
    #
    va
    cA
    wrex
    #
    wph
    @1
    cr
    wcel
    #
    vz
    cv
    #
    vv
    cv
    #
    @8
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
    @12
    vz
    @1
    cC
    vw
    vex
    @19
    @14
    @9
    wceq
    #
    vb
    cB
    wrex
    #
    va
    cA
    wrex
    @14
    @1
    wceq
    #
    @12
    @18
    @21
    vv
    va
    cA
    @15
    @7
    wceq
    #
    @17
    @20
    vb
    cB
    @23
    @16
    @9
    @14
    @15
    @7
    @8
    cmul
    oveq1
    eqeq2d
    rexbidv
    cbvrexv
    @22
    @20
    @10
    va
    vb
    cA
    cB
    @14
    @1
    @9
    eqeq1
    2rexbidv
    syl5bb
    supmul.1
    elab2
    #
    wph
    @10
    @13
    va
    vb
    cA
    cB
    wph
    @7
    cA
    wcel
    #
    @8
    cB
    wcel
    #
    wa
    #
    @9
    cr
    wcel
    #
    @10
    @13
    wi
    wph
    @27
    @7
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    wa
    @28
    wph
    @25
    @29
    @26
    @30
    wph
    cA
    cr
    @7
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
    @2
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
    @2
    cle
    wbr
    #
    vx
    cA
    wral
    @35
    vx
    cB
    wral
    wa
    #
    @31
    @32
    @34
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
    @33
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
    sseld
    wph
    cB
    cr
    @8
    wph
    @38
    @39
    @40
    wph
    @36
    @37
    @41
    supmul.2
    simp3bi
    #
    simp1d
    sseld
    anim12d
    @7
    @8
    remulcl
    syl6
    @9
    cr
    @1
    eleq1a
    syl6
    rexlimdvv
    syl5bi
    ssrdv
    wph
    @12
    vw
    wex
    #
    @0
    wph
    @11
    vw
    wex
    #
    va
    cA
    wrex
    #
    @44
    wph
    @32
    @45
    va
    cA
    wral
    @46
    wph
    @31
    @32
    @34
    @42
    simp2d
    wph
    @45
    va
    cA
    wph
    @10
    vw
    wex
    #
    vb
    cB
    wrex
    #
    @45
    wph
    @39
    @47
    vb
    cB
    wral
    @48
    wph
    @38
    @39
    @40
    @43
    simp2d
    @47
    vb
    cB
    vw
    @9
    @7
    @8
    cmul
    ovex
    isseti
    rgenw
    @47
    vb
    cB
    r19.2z
    sylancl
    @10
    vb
    vw
    cB
    rexcom4
    sylib
    ralrimivw
    @45
    va
    cA
    r19.2z
    syl2anc
    @11
    va
    vw
    cA
    rexcom4
    sylib
    @0
    @6
    vw
    wex
    @44
    vw
    cC
    n0
    @6
    @12
    vw
    @24
    exbii
    bitri
    sylibr
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
    cr
    wcel
    @1
    @51
    cle
    wbr
    #
    vw
    cC
    wral
    #
    @5
    wph
    @49
    @50
    wph
    @37
    @49
    cr
    wcel
    @42
    vx
    vy
    cA
    suprcl
    syl
    wph
    @41
    @50
    cr
    wcel
    @43
    vx
    vy
    cB
    suprcl
    syl
    remulcld
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
    @4
    @53
    vx
    @51
    cr
    @2
    @51
    wceq
    @3
    @52
    vw
    cC
    @2
    @51
    @1
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    3jca
end
