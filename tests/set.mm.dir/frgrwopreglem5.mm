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
include "wceq.mm"
include "simplll.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "simpl.mm"
include "sylbi.mm"
include "crab.mm"
include "rabidim1.mm"
include "eleq2s.mm"
include "anim12i.mm"
include "adantl.mm"
include "cdif.mm"
include "eldifi.mm"
include "frgrwopreglem5lem.mm"
include "adantll.mm"
include "3jca.mm"
include "adantr.mm"
include "frgrwopreglem5a.mm"
include "syl.mm"
include "3anass.mm"
include "sylanbrc.mm"
include "ex.mm"
include "reximdvva.mm"
include "exp31.mm"
include "com24.mm"
include "imp31.mm"
include "com13.mm"
include "imp.mm"
include "cvv.mm"
include "frgrwopreglem1.mm"
include "hashgt12el.mm"
include "im2anan9.mm"
include "ax-mp.mm"
include "syl11.mm"
include "3impib.mm"

theorem frgrwopreglem5
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
    cE
    wcel
    @6
    @4
    cpr
    cE
    wcel
    wa
    #
    @4
    @7
    cpr
    cE
    wcel
    @7
    @3
    cpr
    cE
    wcel
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
    @14
    @1
    @2
    wa
    #
    @15
    @16
    @0
    @14
    wi
    @0
    @16
    @15
    @14
    @0
    @16
    @15
    @14
    wi
    @0
    @16
    wa
    @5
    @13
    va
    vx
    cA
    cA
    @0
    @16
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
    @13
    wi
    @0
    @5
    @21
    @16
    @13
    @0
    @5
    @21
    @16
    @13
    wi
    @0
    @5
    wa
    #
    @21
    wa
    #
    @8
    @12
    vb
    vy
    cB
    cB
    @23
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
    @12
    @27
    @8
    wa
    #
    @9
    @10
    @11
    wa
    #
    @12
    @27
    @5
    @8
    @0
    @5
    @21
    @26
    simpllr
    anim1i
    @28
    @0
    @3
    cV
    wcel
    #
    @4
    cV
    wcel
    #
    wa
    #
    @6
    cV
    wcel
    #
    @7
    cV
    wcel
    #
    wa
    #
    wa
    #
    @3
    cD
    cfv
    #
    @4
    cD
    cfv
    #
    wceq
    @37
    @6
    cD
    cfv
    wne
    @38
    @7
    cD
    cfv
    wne
    w3a
    #
    w3a
    #
    @29
    @27
    @40
    @8
    @27
    @0
    @36
    @39
    @0
    @5
    @21
    @26
    simplll
    @23
    @32
    @26
    @35
    @21
    @32
    @22
    @19
    @30
    @20
    @31
    @19
    @30
    @37
    cK
    wceq
    #
    wa
    @30
    @38
    cK
    wceq
    #
    @41
    vx
    @3
    cV
    cA
    @4
    @3
    wceq
    @38
    @37
    cK
    @4
    @3
    cD
    fveq2
    eqeq1d
    frgrwopreg.a
    elrab2
    @30
    @41
    simpl
    sylbi
    @31
    @4
    @42
    vx
    cV
    crab
    cA
    @42
    vx
    cV
    rabidim1
    frgrwopreg.a
    eleq2s
    anim12i
    adantl
    @24
    @33
    @25
    @34
    @33
    @6
    cV
    cA
    cdif
    #
    cB
    @6
    cV
    cA
    eldifi
    frgrwopreg.b
    eleq2s
    @34
    @7
    @43
    cB
    @7
    cV
    cA
    eldifi
    frgrwopreg.b
    eleq2s
    anim12i
    anim12i
    @21
    @26
    @39
    @22
    vx
    vy
    cA
    cB
    cD
    cE
    cG
    cK
    cV
    va
    vb
    frgrwopreg.v
    frgrwopreg.d
    frgrwopreg.a
    frgrwopreg.b
    frgrwopreg.e
    frgrwopreglem5lem
    adantll
    3jca
    adantr
    @3
    @6
    cD
    cE
    cG
    cV
    @4
    @7
    frgrwopreg.v
    frgrwopreg.d
    frgrwopreg.e
    frgrwopreglem5a
    syl
    @9
    @10
    @11
    3anass
    sylanbrc
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
    @18
    @17
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
    @44
    @1
    @15
    @45
    @2
    @16
    @44
    @1
    @15
    cA
    cvv
    va
    vx
    hashgt12el
    ex
    @45
    @2
    @16
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
