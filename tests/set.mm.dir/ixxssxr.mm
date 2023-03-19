include "co.mm"
include "cxr.mm"
include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "cop.mm"
include "cfv.mm"
include "df-ov.mm"
include "cxp.mm"
include "ixxf.mm"
include "0elpw.mm"
include "f0cli.mm"
include "eqeltri.mm"
include "ovex.mm"
include "elpw.mm"
include "mpbi.mm"

theorem ixxssxr
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
  assert |- ( A O B ) C_ RR*

  proof
    cA
    cB
    cO
    co
    #
    cxr
    cpw
    #
    wcel
    @0
    cxr
    wss
    @0
    cA
    cB
    cop
    #
    cO
    cfv
    @1
    cA
    cB
    cO
    df-ov
    cxr
    cxr
    cxp
    @1
    @2
    cO
    vx
    vy
    vz
    cR
    cS
    cO
    ixx.1
    ixxf
    cxr
    0elpw
    f0cli
    eqeltri
    @0
    cxr
    cA
    cB
    cO
    ovex
    elpw
    mpbi
end
