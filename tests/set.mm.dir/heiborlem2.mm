include "cv.mm"
include "cn0.mm"
include "wcel.mm"
include "cfv.mm"
include "co.mm"
include "w3a.mm"
include "wceq.mm"
include "eleq1.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "3anbi23d.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "oveq2.mm"
include "3anbi123d.mm"
include "brab.mm"

theorem heiborlem2
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let vt: setvar t
  let vx: setvar x
  let vk: setvar k
  let vr: setvar r
  let vg: setvar g
  let wph: wff ph
  let vm: setvar m
  let vz: setvar z
  let cM: class M
  let cT: class T
  let wps: wff ps
  let cS: class S
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume heibor.1: |- J = ( MetOpen ` D )
  assume heibor.3: |- K = { u | -. E. v e. ( ~P U i^i Fin ) u C_ U. v }
  assume heibor.4: |- G = { <. y , n >. | ( n e. NN0 /\ y e. ( F ` n ) /\ ( y B n ) e. K ) }
  assume heiborlem2.5: |- A e. _V
  assume heiborlem2.6: |- C e. _V

  disjoint n y
  disjoint A n
  disjoint A y
  disjoint n u
  disjoint F n
  disjoint u y
  disjoint F u
  disjoint F y
  disjoint n v
  disjoint D n
  disjoint u v
  disjoint D u
  disjoint v y
  disjoint D v
  disjoint D y
  disjoint B n
  disjoint B u
  disjoint B v
  disjoint B y
  disjoint J n
  disjoint J u
  disjoint J v
  disjoint J y
  disjoint U n
  disjoint U u
  disjoint U v
  disjoint U y
  disjoint C n
  disjoint C u
  disjoint C v
  disjoint C y
  disjoint K n
  disjoint K y
  disjoint n t
  disjoint n x
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint x y
  disjoint A x
  disjoint k n
  disjoint k r
  disjoint k t
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint n r
  disjoint r t
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint F r
  disjoint t u
  disjoint F t
  disjoint u x
  disjoint F x
  disjoint g k
  disjoint g t
  disjoint g x
  disjoint G g
  disjoint G k
  disjoint G t
  disjoint G x
  disjoint g r
  disjoint g ph
  disjoint k ph
  disjoint ph r
  disjoint ph t
  disjoint ph x
  disjoint g m
  disjoint g n
  disjoint g u
  disjoint g v
  disjoint g y
  disjoint g z
  disjoint D g
  disjoint k m
  disjoint k v
  disjoint k z
  disjoint D k
  disjoint m n
  disjoint m r
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint n z
  disjoint r v
  disjoint r z
  disjoint D r
  disjoint t v
  disjoint t z
  disjoint D t
  disjoint u z
  disjoint v x
  disjoint v z
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D z
  disjoint M g
  disjoint M k
  disjoint M m
  disjoint M r
  disjoint M t
  disjoint M u
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint T m
  disjoint T n
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint B g
  disjoint B t
  disjoint J g
  disjoint J k
  disjoint J m
  disjoint J r
  disjoint J t
  disjoint J x
  disjoint J z
  disjoint U g
  disjoint U t
  disjoint U x
  disjoint U z
  disjoint g ps
  disjoint ps t
  disjoint ps y
  disjoint ps z
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X g
  disjoint X k
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint C m
  disjoint C t
  disjoint K g
  disjoint K t
  disjoint K x
  disjoint K z
  disjoint Y k
  disjoint Y t
  disjoint Y x
  disjoint Z k
  disjoint Z v
  disjoint Z x
  assert |- ( A G C <-> ( C e. NN0 /\ A e. ( F ` C ) /\ ( A B C ) e. K ) )

  proof
    vn
    cv
    #
    cn0
    wcel
    #
    vy
    cv
    #
    @0
    cF
    cfv
    #
    wcel
    #
    @2
    @0
    cB
    co
    #
    cK
    wcel
    #
    w3a
    @1
    cA
    @3
    wcel
    #
    cA
    @0
    cB
    co
    #
    cK
    wcel
    #
    w3a
    cC
    cn0
    wcel
    #
    cA
    cC
    cF
    cfv
    #
    wcel
    #
    cA
    cC
    cB
    co
    #
    cK
    wcel
    #
    w3a
    vy
    vn
    cA
    cC
    cG
    heiborlem2.5
    heiborlem2.6
    @2
    cA
    wceq
    #
    @4
    @7
    @6
    @9
    @1
    @2
    cA
    @3
    eleq1
    @15
    @5
    @8
    cK
    @2
    cA
    @0
    cB
    oveq1
    eleq1d
    3anbi23d
    @0
    cC
    wceq
    #
    @1
    @10
    @7
    @12
    @9
    @14
    @0
    cC
    cn0
    eleq1
    @16
    @3
    @11
    cA
    @0
    cC
    cF
    fveq2
    eleq2d
    @16
    @8
    @13
    cK
    @0
    cC
    cA
    cB
    oveq2
    eleq1d
    3anbi123d
    heibor.4
    brab
end
