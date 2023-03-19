include "cfrgr.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "wne.mm"
include "wa.mm"
include "cpr.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "simpllr.mm"
include "anim1i.mm"
include "wral.mm"
include "frgrwopreglem4.mm"
include "wceq.mm"
include "preq1.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "cbvralv.mm"
include "rsp2.mm"
include "com12.mm"
include "ad2ant2r.mm"
include "syl5bi.mm"
include "imp.mm"
include "prcom.mm"
include "sylbi.mm"
include "ad2ant2lr.mm"
include "syl5eqel.mm"
include "jca.mm"
include "expcom.mm"
include "syl.mm"
include "adantr.mm"
include "impl.mm"
include "preq2.mm"
include "rspc2v.mm"
include "ad2ant2l.mm"
include "impcom.mm"
include "ad2ant2rl.mm"
include "ex.mm"
include "3jca.mm"
include "reximdvva.mm"
include "exp31.mm"
include "com24.mm"
include "imp31.mm"
include "com13.mm"
include "cvv.mm"
include "frgrwopreglem1.mm"
include "hashgt12el.mm"
include "im2anan9.mm"
include "ax-mp.mm"
include "syl11.mm"
include "3impib.mm"

theorem frgrwopreglem5ALT
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cE: class E
  let cG: class G
  let cK: class K
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vv: setvar v
  let vw: setvar w
  let cX: class X
  let vz: setvar z
  let cY: class Y
  assume frgrwopreg.v: |- V = ( Vtx ` G )
  assume frgrwopreg.d: |- D = ( VtxDeg ` G )
  assume frgrwopreg.a: |- A = { x e. V | ( D ` x ) = K }
  assume frgrwopreg.b: |- B = ( V \ A )
  assume frgrwopreg.e: |- E = ( Edg ` G )

  disjoint A b
  disjoint B x
  disjoint D y
  disjoint G a
  disjoint G b
  disjoint G x
  disjoint G y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint x y
  disjoint V y
  disjoint A x
  disjoint A a
  disjoint A y
  disjoint B a
  disjoint B b
  disjoint B y
  disjoint E x
  disjoint E a
  disjoint E b
  disjoint V x
  disjoint A x
  disjoint G x
  disjoint K x
  disjoint D x
  disjoint A v
  disjoint A w
  disjoint v w
  disjoint B v
  disjoint B w
  disjoint E v
  disjoint G v
  disjoint G w
  disjoint v x
  disjoint w x
  disjoint V w
  disjoint X v
  disjoint X w
  disjoint V v
  disjoint A z
  disjoint x z
  disjoint D z
  disjoint G z
  disjoint K z
  disjoint V z
  disjoint y z
  disjoint B z
  disjoint a z
  disjoint b z
  disjoint E z
  disjoint X x
  disjoint Y x
  assert |- ( ( G e. FriendGraph /\ 1 < ( # ` A ) /\ 1 < ( # ` B ) ) -> E. a e. A E. x e. A E. b e. B E. y e. B ( ( a =/= x /\ b =/= y ) /\ ( { a , b } e. E /\ { b , x } e. E ) /\ ( { x , y } e. E /\ { y , a } e. E ) ) )

  proof
    cG
    cfrgr
    wcel
    #
    c1
    cA
    chash
    cfv
    clt
    wbr
    #
    c1
    cB
    chash
    cfv
    clt
    wbr
    #
    va
    cv
    #
    vx
    cv
    #
    wne
    #
    vb
    cv
    #
    vy
    cv
    #
    wne
    #
    wa
    #
    @3
    @6
    cpr
    #
    cE
    wcel
    #
    @6
    @4
    cpr
    #
    cE
    wcel
    #
    wa
    #
    @4
    @7
    cpr
    #
    cE
    wcel
    #
    @7
    @3
    cpr
    #
    cE
    wcel
    #
    wa
    #
    w3a
    #
    vy
    cB
    wrex
    vb
    cB
    wrex
    #
    vx
    cA
    wrex
    va
    cA
    wrex
    #
    @5
    vx
    cA
    wrex
    va
    cA
    wrex
    #
    @8
    vy
    cB
    wrex
    vb
    cB
    wrex
    #
    wa
    #
    @0
    @22
    @1
    @2
    wa
    #
    @23
    @24
    @0
    @22
    wi
    @0
    @24
    @23
    @22
    @0
    @24
    @23
    @22
    wi
    @0
    @24
    wa
    @5
    @21
    va
    vx
    cA
    cA
    @0
    @24
    @3
    cA
    wcel
    #
    @4
    cA
    wcel
    #
    wa
    #
    @5
    @21
    wi
    @0
    @5
    @29
    @24
    @21
    @0
    @5
    @29
    @24
    @21
    wi
    @0
    @5
    wa
    #
    @29
    wa
    #
    @8
    @20
    vb
    vy
    cB
    cB
    @31
    @6
    cB
    wcel
    #
    @7
    cB
    wcel
    #
    wa
    #
    wa
    #
    @8
    @20
    @35
    @8
    wa
    @9
    @14
    @19
    @35
    @5
    @8
    @0
    @5
    @29
    @34
    simpllr
    anim1i
    @35
    @14
    @8
    @30
    @29
    @34
    @14
    @0
    @29
    @34
    wa
    #
    @14
    wi
    #
    @5
    @0
    vz
    cv
    #
    @6
    cpr
    #
    cE
    wcel
    #
    vb
    cB
    wral
    #
    vz
    cA
    wral
    #
    @37
    vx
    cA
    cB
    cD
    cE
    cG
    cK
    cV
    vz
    vb
    frgrwopreg.v
    frgrwopreg.d
    frgrwopreg.a
    frgrwopreg.b
    frgrwopreg.e
    frgrwopreglem4
    #
    @36
    @42
    @14
    @36
    @42
    wa
    #
    @11
    @13
    @36
    @42
    @11
    @42
    @11
    vb
    cB
    wral
    #
    va
    cA
    wral
    #
    @36
    @11
    @41
    @45
    vz
    va
    cA
    @38
    @3
    wceq
    #
    @40
    @11
    vb
    cB
    @47
    @39
    @10
    cE
    @38
    @3
    @6
    preq1
    eleq1d
    #
    ralbidv
    cbvralv
    @27
    @32
    @46
    @11
    wi
    @28
    @33
    @46
    @27
    @32
    wa
    @11
    @11
    va
    vb
    cA
    cB
    rsp2
    com12
    ad2ant2r
    syl5bi
    imp
    @44
    @12
    @4
    @6
    cpr
    #
    cE
    @6
    @4
    prcom
    @36
    @42
    @49
    cE
    wcel
    #
    @28
    @32
    @42
    @50
    wi
    @27
    @33
    @42
    @28
    @32
    wa
    #
    @50
    @42
    @50
    vb
    cB
    wral
    #
    vx
    cA
    wral
    @51
    @50
    wi
    @41
    @52
    vz
    vx
    cA
    @38
    @4
    wceq
    #
    @40
    @50
    vb
    cB
    @53
    @39
    @49
    cE
    @38
    @4
    @6
    preq1
    eleq1d
    #
    ralbidv
    cbvralv
    @50
    vx
    vb
    cA
    cB
    rsp2
    sylbi
    com12
    ad2ant2lr
    imp
    syl5eqel
    jca
    expcom
    syl
    adantr
    impl
    adantr
    @35
    @19
    @8
    @30
    @29
    @34
    @19
    @0
    @36
    @19
    wi
    #
    @5
    @0
    @42
    @55
    @43
    @42
    @36
    @19
    @42
    @36
    wa
    #
    @16
    @18
    @36
    @42
    @16
    @28
    @33
    @42
    @16
    wi
    @27
    @32
    @40
    @16
    @50
    vz
    vb
    @4
    @7
    cA
    cB
    @54
    @6
    @7
    wceq
    #
    @49
    @15
    cE
    @6
    @7
    @4
    preq2
    eleq1d
    rspc2v
    ad2ant2l
    impcom
    @56
    @17
    @3
    @7
    cpr
    #
    cE
    @7
    @3
    prcom
    @36
    @42
    @58
    cE
    wcel
    #
    @27
    @33
    @42
    @59
    wi
    @28
    @32
    @40
    @59
    @11
    vz
    vb
    @3
    @7
    cA
    cB
    @48
    @57
    @10
    @58
    cE
    @6
    @7
    @3
    preq2
    eleq1d
    rspc2v
    ad2ant2rl
    impcom
    syl5eqel
    jca
    ex
    syl
    adantr
    impl
    adantr
    3jca
    ex
    reximdvva
    exp31
    com24
    imp31
    reximdvva
    ex
    com13
    imp
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    @26
    @25
    wi
    vx
    cA
    cB
    cD
    cG
    cK
    cV
    frgrwopreg.v
    frgrwopreg.d
    frgrwopreg.a
    frgrwopreg.b
    frgrwopreglem1
    @60
    @1
    @23
    @61
    @2
    @24
    @60
    @1
    @23
    cA
    cvv
    va
    vx
    hashgt12el
    ex
    @61
    @2
    @24
    cB
    cvv
    vb
    vy
    hashgt12el
    ex
    im2anan9
    ax-mp
    syl11
    3impib
end
