include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cin.mm"
include "c0.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "elin.mm"
include "wbr.mm"
include "wb.mm"
include "elixx1.mm"
include "3adant3.mm"
include "biimpa.mm"
include "simp3d.mm"
include "adantrr.mm"
include "wn.mm"
include "3adant1.mm"
include "simp2d.mm"
include "simpl2.mm"
include "simp1d.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "adantrl.mm"
include "pm2.65da.mm"
include "pm2.21d.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "ss0.mm"
include "syl.mm"

theorem ixxdisj
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
  let cU: class U
  let cO: class O
  let cD: class D
  let cQ: class Q
  let cW: class W
  let cX: class X
  assume ixx.1: |- O = ( x e. RR* , y e. RR* |-> { z e. RR* | ( x R z /\ z S y ) } )
  assume ixxun.2: |- P = ( x e. RR* , y e. RR* |-> { z e. RR* | ( x T z /\ z U y ) } )
  assume ixxun.3: |- ( ( B e. RR* /\ w e. RR* ) -> ( B T w <-> -. w S B ) )

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
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint Q w
  disjoint W w
  disjoint X w
  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) -> ( ( A O B ) i^i ( B P C ) ) = (/) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    #
    cA
    cB
    cO
    co
    #
    cB
    cC
    cP
    co
    #
    cin
    #
    c0
    wss
    @6
    c0
    wceq
    @3
    vw
    @6
    c0
    vw
    cv
    #
    @6
    wcel
    @7
    @4
    wcel
    #
    @7
    @5
    wcel
    #
    wa
    #
    @3
    @7
    c0
    wcel
    #
    @7
    @4
    @5
    elin
    @3
    @10
    @11
    @3
    @10
    @7
    cB
    cS
    wbr
    #
    @3
    @8
    @12
    @9
    @3
    @8
    wa
    @7
    cxr
    wcel
    #
    cA
    @7
    cR
    wbr
    #
    @12
    @3
    @8
    @13
    @14
    @12
    w3a
    #
    @0
    @1
    @8
    @15
    wb
    @2
    vx
    vy
    vz
    cA
    cB
    @7
    cR
    cS
    cO
    ixx.1
    elixx1
    3adant3
    biimpa
    simp3d
    adantrr
    @3
    @9
    @12
    wn
    #
    @8
    @3
    @9
    wa
    #
    cB
    @7
    cT
    wbr
    #
    @16
    @17
    @13
    @18
    @7
    cC
    cU
    wbr
    #
    @3
    @9
    @13
    @18
    @19
    w3a
    #
    @1
    @2
    @9
    @20
    wb
    @0
    vx
    vy
    vz
    cB
    cC
    @7
    cT
    cU
    cP
    ixxun.2
    elixx1
    3adant1
    biimpa
    #
    simp2d
    @17
    @1
    @13
    @18
    @16
    wb
    @0
    @1
    @2
    @9
    simpl2
    @17
    @13
    @18
    @19
    @21
    simp1d
    ixxun.3
    syl2anc
    mpbid
    adantrl
    pm2.65da
    pm2.21d
    syl5bi
    ssrdv
    @6
    ss0
    syl
end
