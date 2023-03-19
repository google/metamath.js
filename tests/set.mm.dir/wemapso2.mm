include "cvv.mm"
include "wcel.mm"
include "wor.mm"
include "w3a.mm"
include "wi.mm"
include "wemapso2lem.mm"
include "expcom.mm"
include "wn.mm"
include "c0.mm"
include "so0.mm"
include "wceq.mm"
include "wb.mm"
include "cv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "wral.mm"
include "relfsupp.mm"
include "brrelex2i.mm"
include "con3i.mm"
include "ralrimivw.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "syl5eq.mm"
include "soeq2.mm"
include "syl.mm"
include "mpbiri.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem wemapso2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cV: class V
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cX: class X
  let cP: class P
  let cQ: class Q
  let cW: class W
  assume wemapso.t: |- T = { <. x , y >. | E. z e. A ( ( x ` z ) S ( y ` z ) /\ A. w e. A ( w R z -> ( x ` w ) = ( y ` w ) ) ) }
  assume wemapso2.u: |- U = { x e. ( B ^m A ) | x finSupp Z }

  disjoint B x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint Z x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint B b
  disjoint c d
  disjoint c x
  disjoint B c
  disjoint d x
  disjoint B d
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U d
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint X a
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint X b
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint X c
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint A d
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q a
  disjoint Q b
  disjoint Q c
  disjoint Q d
  disjoint Q w
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint Z c
  disjoint Z d
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V d
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W d
  disjoint Z a
  disjoint Z b
  assert |- ( ( A e. V /\ R Or A /\ S Or B ) -> T Or U )

  proof
    cZ
    cvv
    wcel
    #
    cA
    cV
    wcel
    cA
    cR
    wor
    cB
    cS
    wor
    w3a
    #
    cU
    cT
    wor
    #
    wi
    @1
    @0
    @2
    vx
    vy
    vz
    vw
    cA
    cB
    cR
    cS
    cT
    cU
    cV
    cvv
    cZ
    wemapso.t
    wemapso2.u
    wemapso2lem
    expcom
    @0
    wn
    #
    @2
    @1
    @3
    @2
    c0
    cT
    wor
    #
    cT
    so0
    @3
    cU
    c0
    wceq
    @2
    @4
    wb
    @3
    cU
    vx
    cv
    #
    cZ
    cfsupp
    wbr
    #
    vx
    cB
    cA
    cmap
    co
    #
    crab
    #
    c0
    wemapso2.u
    @3
    @6
    wn
    #
    vx
    @7
    wral
    @8
    c0
    wceq
    @3
    @9
    vx
    @7
    @6
    @0
    @5
    cZ
    cfsupp
    relfsupp
    brrelex2i
    con3i
    ralrimivw
    @6
    vx
    @7
    rabeq0
    sylibr
    syl5eq
    cU
    c0
    cT
    soeq2
    syl
    mpbiri
    a1d
    pm2.61i
end
