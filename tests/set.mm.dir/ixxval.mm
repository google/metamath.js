include "cxr.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "crab.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi1d.mm"
include "rabbidv.mm"
include "breq2.mm"
include "anbi2d.mm"
include "xrex.mm"
include "rabex.mm"
include "ovmpt2.mm"

theorem ixxval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cO: class O
  let vw: setvar w
  let cC: class C
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
  disjoint C x
  disjoint C y
  disjoint C z
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
  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A O B ) = { z e. RR* | ( A R z /\ z S B ) } )

  proof
    vx
    vy
    cA
    cB
    cxr
    cxr
    vx
    cv
    #
    vz
    cv
    #
    cR
    wbr
    #
    @1
    vy
    cv
    #
    cS
    wbr
    #
    wa
    #
    vz
    cxr
    crab
    cA
    @1
    cR
    wbr
    #
    @1
    cB
    cS
    wbr
    #
    wa
    #
    vz
    cxr
    crab
    cO
    @6
    @4
    wa
    #
    vz
    cxr
    crab
    @0
    cA
    wceq
    #
    @5
    @9
    vz
    cxr
    @10
    @2
    @6
    @4
    @0
    cA
    @1
    cR
    breq1
    anbi1d
    rabbidv
    @3
    cB
    wceq
    #
    @9
    @8
    vz
    cxr
    @11
    @4
    @7
    @6
    @3
    cB
    @1
    cS
    breq2
    anbi2d
    rabbidv
    ixx.1
    @8
    vz
    cxr
    xrex
    rabex
    ovmpt2
end
