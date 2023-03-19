include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "w3a.mm"
include "co.mm"
include "anass.mm"
include "df-3an.mm"
include "anbi1i.mm"
include "wb.mm"
include "elixx1.mm"
include "3anass.mm"
include "ibar.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "wn.mm"
include "c0.mm"
include "cxp.mm"
include "cpw.mm"
include "ixxf.mm"
include "fdmi.mm"
include "ndmov.mm"
include "eleq2d.mm"
include "noel.mm"
include "pm2.21i.mm"
include "simpl.mm"
include "pm5.21ni.mm"
include "pm2.61i.mm"
include "3bitr4ri.mm"

theorem elixx3g
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
  assert |- ( C e. ( A O B ) <-> ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ ( A R C /\ C S B ) ) )

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
    cC
    cxr
    wcel
    #
    wa
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
    wa
    #
    wa
    @2
    @3
    @7
    wa
    #
    wa
    #
    @0
    @1
    @3
    w3a
    #
    @7
    wa
    cC
    cA
    cB
    cO
    co
    #
    wcel
    #
    @2
    @3
    @7
    anass
    @10
    @4
    @7
    @0
    @1
    @3
    df-3an
    anbi1i
    @2
    @12
    @9
    wb
    @2
    @12
    @3
    @5
    @6
    w3a
    #
    @9
    vx
    vy
    vz
    cA
    cB
    cC
    cR
    cS
    cO
    ixx.1
    elixx1
    @13
    @8
    @2
    @9
    @3
    @5
    @6
    3anass
    @2
    @8
    ibar
    syl5bb
    bitrd
    @2
    wn
    #
    @12
    cC
    c0
    wcel
    #
    @9
    @14
    @11
    c0
    cC
    cA
    cB
    cxr
    cO
    cxr
    cxr
    cxp
    cxr
    cpw
    cO
    vx
    vy
    vz
    cR
    cS
    cO
    ixx.1
    ixxf
    fdmi
    ndmov
    eleq2d
    @15
    @2
    @9
    @15
    @2
    cC
    noel
    pm2.21i
    @2
    @8
    simpl
    pm5.21ni
    bitrd
    pm2.61i
    3bitr4ri
end
