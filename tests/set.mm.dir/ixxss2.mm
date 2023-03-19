include "cxr.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "w3a.mm"
include "elixx3g.mm"
include "simplbi.mm"
include "adantl.mm"
include "simp3d.mm"
include "simprbi.mm"
include "simpld.mm"
include "simprd.mm"
include "simplr.mm"
include "wi.mm"
include "simp2d.mm"
include "simpll.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "wb.mm"
include "simp1d.mm"
include "elixx1.mm"
include "syl2anc.mm"
include "mpbir3and.mm"
include "ex.mm"
include "ssrdv.mm"

theorem ixxss2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cO: class O
  let cW: class W
  let cD: class D
  let cQ: class Q
  let cU: class U
  let cX: class X
  assume ixx.1: |- O = ( x e. RR* , y e. RR* |-> { z e. RR* | ( x R z /\ z S y ) } )
  assume ixxss2.2: |- P = ( x e. RR* , y e. RR* |-> { z e. RR* | ( x R z /\ z T y ) } )
  assume ixxss2.3: |- ( ( w e. RR* /\ B e. RR* /\ C e. RR* ) -> ( ( w T B /\ B W C ) -> w S C ) )

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
  disjoint W w
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint Q w
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint X w
  assert |- ( ( C e. RR* /\ B W C ) -> ( A P B ) C_ ( A O C ) )

  proof
    cC
    cxr
    wcel
    #
    cB
    cC
    cW
    wbr
    #
    wa
    #
    vw
    cA
    cB
    cP
    co
    #
    cA
    cC
    cO
    co
    #
    @2
    vw
    cv
    #
    @3
    wcel
    #
    @5
    @4
    wcel
    #
    @2
    @6
    wa
    #
    @7
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
    cC
    cS
    wbr
    #
    @8
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @9
    @6
    @12
    @13
    @9
    w3a
    #
    @2
    @6
    @14
    @10
    @5
    cB
    cT
    wbr
    #
    wa
    #
    vx
    vy
    vz
    cA
    cB
    @5
    cR
    cT
    cP
    ixxss2.2
    elixx3g
    #
    simplbi
    adantl
    #
    simp3d
    #
    @8
    @10
    @15
    @6
    @16
    @2
    @6
    @14
    @16
    @17
    simprbi
    adantl
    #
    simpld
    @8
    @15
    @1
    @11
    @8
    @10
    @15
    @20
    simprd
    @0
    @1
    @6
    simplr
    @8
    @9
    @13
    @0
    @15
    @1
    wa
    @11
    wi
    @19
    @8
    @12
    @13
    @9
    @18
    simp2d
    @0
    @1
    @6
    simpll
    #
    ixxss2.3
    syl3anc
    mp2and
    @8
    @12
    @0
    @7
    @9
    @10
    @11
    w3a
    wb
    @8
    @12
    @13
    @9
    @18
    simp1d
    @21
    vx
    vy
    vz
    cA
    cC
    @5
    cR
    cS
    cO
    ixx.1
    elixx1
    syl2anc
    mpbir3and
    ex
    ssrdv
end
