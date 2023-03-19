include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "w3a.mm"
include "ixxval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "elrab.mm"
include "3anass.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem elixx1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cO: class O
  let vw: setvar w
  let cD: class D
  let cQ: class Q
  let cP: class P
  let cT: class T
  let cU: class U
  let cW: class W
  let cX: class X
  assume ixx.1: |- O = ( x e. RR* , y e. RR* |-> { z e. RR* | ( x R z /\ z S y ) } )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint C w
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint O w
  disjoint Q w
  disjoint B w
  disjoint P w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint W w
  disjoint X w
  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( C e. ( A O B ) <-> ( C e. RR* /\ A R C /\ C S B ) ) )

  proof
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    wa
    #
    cC
    cA
    cB
    cO
    co
    #
    wcel
    cC
    cA
    vz
    cv
    #
    cR
    wbr
    #
    @2
    cB
    cS
    wbr
    #
    wa
    #
    vz
    cxr
    crab
    #
    wcel
    #
    cC
    cxr
    wcel
    #
    cA
    cC
    cR
    wbr
    #
    cC
    cB
    cS
    wbr
    #
    w3a
    #
    @0
    @1
    @6
    cC
    vx
    vy
    vz
    cA
    cB
    cR
    cS
    cO
    ixx.1
    ixxval
    eleq2d
    @7
    @8
    @9
    @10
    wa
    #
    wa
    @11
    @5
    @12
    vz
    cC
    cxr
    @2
    cC
    wceq
    @3
    @9
    @4
    @10
    @2
    cC
    cA
    cR
    breq2
    @2
    cC
    cB
    cS
    breq1
    anbi12d
    elrab
    @8
    @9
    @10
    3anass
    bitr4i
    syl6bb
end
