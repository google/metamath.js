include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "cv.mm"
include "w3a.mm"
include "elixx3g.mm"
include "simplbi.mm"
include "adantl.mm"
include "simp3d.mm"
include "simplrl.mm"
include "simprbi.mm"
include "simpld.mm"
include "wi.mm"
include "simplll.mm"
include "simp1d.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "simprd.mm"
include "simplrr.mm"
include "simp2d.mm"
include "simpllr.mm"
include "wb.mm"
include "elixx1.mm"
include "ad2antrr.mm"
include "mpbir3and.mm"
include "ex.mm"
include "ssrdv.mm"

theorem ixxss12
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cO: class O
  let cW: class W
  let cX: class X
  let cQ: class Q
  assume ixx.1: |- O = ( x e. RR* , y e. RR* |-> { z e. RR* | ( x R z /\ z S y ) } )
  assume ixxss12.2: |- P = ( x e. RR* , y e. RR* |-> { z e. RR* | ( x T z /\ z U y ) } )
  assume ixxss12.3: |- ( ( A e. RR* /\ C e. RR* /\ w e. RR* ) -> ( ( A W C /\ C T w ) -> A R w ) )
  assume ixxss12.4: |- ( ( w e. RR* /\ D e. RR* /\ B e. RR* ) -> ( ( w U D /\ D X B ) -> w S B ) )

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
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
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
  disjoint W w
  disjoint X w
  disjoint Q w
  assert |- ( ( ( A e. RR* /\ B e. RR* ) /\ ( A W C /\ D X B ) ) -> ( C P D ) C_ ( A O B ) )

  proof
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
    cA
    cC
    cW
    wbr
    #
    cD
    cB
    cX
    wbr
    #
    wa
    #
    wa
    #
    vw
    cC
    cD
    cP
    co
    #
    cA
    cB
    cO
    co
    #
    @6
    vw
    cv
    #
    @7
    wcel
    #
    @9
    @8
    wcel
    #
    @6
    @10
    wa
    #
    @11
    @9
    cxr
    wcel
    #
    cA
    @9
    cR
    wbr
    #
    @9
    cB
    cS
    wbr
    #
    @12
    cC
    cxr
    wcel
    #
    cD
    cxr
    wcel
    #
    @13
    @10
    @16
    @17
    @13
    w3a
    #
    @6
    @10
    @18
    cC
    @9
    cT
    wbr
    #
    @9
    cD
    cU
    wbr
    #
    wa
    #
    vx
    vy
    vz
    cC
    cD
    @9
    cT
    cU
    cP
    ixxss12.2
    elixx3g
    #
    simplbi
    adantl
    #
    simp3d
    #
    @12
    @3
    @19
    @14
    @2
    @3
    @4
    @10
    simplrl
    @12
    @19
    @20
    @10
    @21
    @6
    @10
    @18
    @21
    @22
    simprbi
    adantl
    #
    simpld
    @12
    @0
    @16
    @13
    @3
    @19
    wa
    @14
    wi
    @0
    @1
    @5
    @10
    simplll
    @12
    @16
    @17
    @13
    @23
    simp1d
    @24
    ixxss12.3
    syl3anc
    mp2and
    @12
    @20
    @4
    @15
    @12
    @19
    @20
    @25
    simprd
    @2
    @3
    @4
    @10
    simplrr
    @12
    @13
    @17
    @1
    @20
    @4
    wa
    @15
    wi
    @24
    @12
    @16
    @17
    @13
    @23
    simp2d
    @0
    @1
    @5
    @10
    simpllr
    ixxss12.4
    syl3anc
    mp2and
    @2
    @11
    @13
    @14
    @15
    w3a
    wb
    @5
    @10
    vx
    vy
    vz
    cA
    cB
    @9
    cR
    cS
    cO
    ixx.1
    elixx1
    ad2antrr
    mpbir3and
    ex
    ssrdv
end
