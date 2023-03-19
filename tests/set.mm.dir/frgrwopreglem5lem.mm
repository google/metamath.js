include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wne.mm"
include "rabeq2i.mm"
include "wi.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "eqtr3.mm"
include "expcom.mm"
include "adantl.mm"
include "com12.mm"
include "simplbiim.mm"
include "syl5bi.mm"
include "imp.mm"
include "adantr.mm"
include "frgrwopreglem3.mm"
include "ad2ant2r.mm"
include "crab.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "ad2ant2l.mm"
include "3jca.mm"

theorem frgrwopreglem5lem
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
  disjoint X x
  disjoint Y x
  assert |- ( ( ( a e. A /\ x e. A ) /\ ( b e. B /\ y e. B ) ) -> ( ( D ` a ) = ( D ` x ) /\ ( D ` a ) =/= ( D ` b ) /\ ( D ` x ) =/= ( D ` y ) ) )

  proof
    va
    cv
    #
    cA
    wcel
    #
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    vb
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    wa
    @0
    cD
    cfv
    #
    @2
    cD
    cfv
    #
    wceq
    #
    @10
    @5
    cD
    cfv
    wne
    #
    @11
    @7
    cD
    cfv
    wne
    #
    @4
    @12
    @9
    @1
    @3
    @12
    @3
    @2
    cV
    wcel
    #
    @11
    cK
    wceq
    #
    wa
    #
    @1
    @12
    @16
    vx
    cA
    cV
    frgrwopreg.a
    rabeq2i
    @1
    @0
    cV
    wcel
    @10
    cK
    wceq
    #
    @17
    @12
    wi
    @16
    @18
    vx
    @0
    cV
    cA
    @2
    @0
    wceq
    @11
    @10
    cK
    @2
    @0
    cD
    fveq2
    eqeq1d
    frgrwopreg.a
    elrab2
    @17
    @18
    @12
    @16
    @18
    @12
    wi
    @15
    @18
    @16
    @12
    @10
    @11
    cK
    eqtr3
    expcom
    adantl
    com12
    simplbiim
    syl5bi
    imp
    adantr
    @1
    @6
    @13
    @3
    @8
    vx
    cA
    cB
    cD
    cG
    cK
    cV
    @0
    @5
    frgrwopreg.v
    frgrwopreg.d
    frgrwopreg.a
    frgrwopreg.b
    frgrwopreglem3
    ad2ant2r
    @3
    @8
    @14
    @1
    @6
    vz
    cA
    cB
    cD
    cG
    cK
    cV
    @2
    @7
    frgrwopreg.v
    frgrwopreg.d
    cA
    @16
    vx
    cV
    crab
    vz
    cv
    #
    cD
    cfv
    #
    cK
    wceq
    #
    vz
    cV
    crab
    frgrwopreg.a
    @16
    @21
    vx
    vz
    cV
    @2
    @19
    wceq
    @11
    @20
    cK
    @2
    @19
    cD
    fveq2
    eqeq1d
    cbvrabv
    eqtri
    frgrwopreg.b
    frgrwopreglem3
    ad2ant2l
    3jca
end
