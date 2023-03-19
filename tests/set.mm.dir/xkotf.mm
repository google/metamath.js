include "cv.mm"
include "cima.mm"
include "wss.mm"
include "ccn.mm"
include "co.mm"
include "crab.mm"
include "cpw.mm"
include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "ssrab2.mm"
include "ovex.mm"
include "elpw2.mm"
include "mpbir.mm"
include "rgen2w.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem xkotf
  let vx: setvar x
  let vv: setvar v
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vk: setvar k
  let cK: class K
  let cX: class X
  let vs: setvar s
  let vr: setvar r
  assume xkoval.x: |- X = U. R
  assume xkoval.k: |- K = { x e. ~P X | ( R |`t x ) e. Comp }
  assume xkoval.t: |- T = ( k e. K , v e. S |-> { f e. ( R Cn S ) | ( f " k ) C_ v } )

  disjoint k v
  disjoint K k
  disjoint K v
  disjoint f k
  disjoint f v
  disjoint f x
  disjoint R f
  disjoint k x
  disjoint R k
  disjoint v x
  disjoint R v
  disjoint R x
  disjoint S f
  disjoint S k
  disjoint S v
  disjoint S x
  disjoint X k
  disjoint X x
  disjoint k s
  disjoint s v
  disjoint K s
  disjoint f r
  disjoint f s
  disjoint k r
  disjoint r s
  disjoint r v
  disjoint r x
  disjoint R r
  disjoint s x
  disjoint R s
  disjoint S r
  disjoint S s
  disjoint T r
  disjoint T s
  assert |- T : ( K X. S ) --> ~P ( R Cn S )

  proof
    vf
    cv
    vk
    cv
    cima
    vv
    cv
    wss
    #
    vf
    cR
    cS
    ccn
    co
    #
    crab
    #
    @1
    cpw
    #
    wcel
    #
    vv
    cS
    wral
    vk
    cK
    wral
    cK
    cS
    cxp
    @3
    cT
    wf
    @4
    vk
    vv
    cK
    cS
    @4
    @2
    @1
    wss
    @0
    vf
    @1
    ssrab2
    @2
    @1
    cR
    cS
    ccn
    ovex
    elpw2
    mpbir
    rgen2w
    vk
    vv
    cK
    cS
    @2
    @3
    cT
    xkoval.t
    fmpt2
    mpbi
end
