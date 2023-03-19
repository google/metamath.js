include "cxr.mm"
include "cxp.mm"
include "cpw.mm"
include "xrex.mm"
include "xpex.mm"
include "pwex.mm"
include "wf.mm"
include "wss.mm"
include "ixxf.mm"
include "fssxp.mm"
include "ax-mp.mm"
include "ssexi.mm"

theorem ixxex
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cS: class S
  let cO: class O
  let vw: setvar w
  let cA: class A
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cB: class B
  let cP: class P
  let cT: class T
  let cU: class U
  let cW: class W
  let cX: class X
  assume ixx.1: |- O = ( x e. RR* , y e. RR* |-> { z e. RR* | ( x R z /\ z S y ) } )

  disjoint x y
  disjoint x z
  disjoint y z
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
  disjoint A x
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
  disjoint Q w
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint P w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint W w
  disjoint X w
  assert |- O e. _V

  proof
    cO
    cxr
    cxr
    cxp
    #
    cxr
    cpw
    #
    cxp
    #
    @0
    @1
    cxr
    cxr
    xrex
    xrex
    xpex
    cxr
    xrex
    pwex
    xpex
    @0
    @1
    cO
    wf
    cO
    @2
    wss
    vx
    vy
    vz
    cR
    cS
    cO
    ixx.1
    ixxf
    @0
    @1
    cO
    fssxp
    ax-mp
    ssexi
end
