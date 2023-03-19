include "co.mm"
include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "elmpt2cl.mm"
include "w3a.mm"
include "wi.mm"
include "simp1.mm"
include "a1i.mm"
include "simpl.mm"
include "3simpa.mm"
include "expimpd.mm"
include "syl2im.mm"
include "simpr.mm"
include "3simpb.mm"
include "ancoms.mm"
include "3jcad.mm"
include "elixx1.mm"
include "3imtr4d.mm"
include "mpcom.mm"
include "ssriv.mm"

theorem ixxssixx
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cO: class O
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cW: class W
  let cX: class X
  assume ixx.1: |- O = ( x e. RR* , y e. RR* |-> { z e. RR* | ( x R z /\ z S y ) } )
  assume ixx.2: |- P = ( x e. RR* , y e. RR* |-> { z e. RR* | ( x T z /\ z U y ) } )
  assume ixx.3: |- ( ( A e. RR* /\ w e. RR* ) -> ( A R w -> A T w ) )
  assume ixx.4: |- ( ( w e. RR* /\ B e. RR* ) -> ( w S B -> w U B ) )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint O w
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint P w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint Q w
  disjoint W w
  disjoint X w
  assert |- ( A O B ) C_ ( A P B )

  proof
    vw
    cA
    cB
    cO
    co
    #
    cA
    cB
    cP
    co
    #
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    vw
    cv
    #
    @0
    wcel
    #
    @5
    @1
    wcel
    #
    vx
    vy
    cxr
    cxr
    vx
    cv
    vz
    cv
    #
    cR
    wbr
    @8
    vy
    cv
    cS
    wbr
    wa
    vz
    cxr
    crab
    cA
    cB
    cO
    @5
    ixx.1
    elmpt2cl
    @4
    @5
    cxr
    wcel
    #
    cA
    @5
    cR
    wbr
    #
    @5
    cB
    cS
    wbr
    #
    w3a
    #
    @9
    cA
    @5
    cT
    wbr
    #
    @5
    cB
    cU
    wbr
    #
    w3a
    @6
    @7
    @4
    @12
    @9
    @13
    @14
    @12
    @9
    wi
    @4
    @9
    @10
    @11
    simp1
    a1i
    @4
    @2
    @12
    @9
    @10
    wa
    @13
    @2
    @3
    simpl
    @9
    @10
    @11
    3simpa
    @2
    @9
    @10
    @13
    ixx.3
    expimpd
    syl2im
    @4
    @3
    @12
    @9
    @11
    wa
    @14
    @2
    @3
    simpr
    @9
    @10
    @11
    3simpb
    @3
    @9
    @11
    @14
    @9
    @3
    @11
    @14
    wi
    ixx.4
    ancoms
    expimpd
    syl2im
    3jcad
    vx
    vy
    vz
    cA
    cB
    @5
    cR
    cS
    cO
    ixx.1
    elixx1
    vx
    vy
    vz
    cA
    cB
    @5
    cT
    cU
    cP
    ixx.2
    elixx1
    3imtr4d
    mpcom
    ssriv
end
