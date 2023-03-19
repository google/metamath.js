include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "cxr.mm"
include "crab.mm"
include "cpw.mm"
include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "wss.mm"
include "ssrab2.mm"
include "xrex.mm"
include "elpw2.mm"
include "mpbir.mm"
include "rgen2w.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem ixxf
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
  assert |- O : ( RR* X. RR* ) --> ~P RR*

  proof
    vx
    cv
    vz
    cv
    #
    cR
    wbr
    @0
    vy
    cv
    cS
    wbr
    wa
    #
    vz
    cxr
    crab
    #
    cxr
    cpw
    #
    wcel
    #
    vy
    cxr
    wral
    vx
    cxr
    wral
    cxr
    cxr
    cxp
    @3
    cO
    wf
    @4
    vx
    vy
    cxr
    cxr
    @4
    @2
    cxr
    wss
    @1
    vz
    cxr
    ssrab2
    @2
    cxr
    xrex
    elpw2
    mpbir
    rgen2w
    vx
    vy
    cxr
    cxr
    @2
    @3
    cO
    ixx.1
    fmpt2
    mpbi
end
