include "crn.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "ccn.mm"
include "co.mm"
include "crab.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "crest.mm"
include "ccmp.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "rnmpt2.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "rexrab.mm"
include "rexeqi.mm"
include "r19.42v.mm"
include "rexbii.mm"
include "3bitr4i.mm"
include "abbii.mm"
include "eqtri.mm"

theorem xkobval
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

  disjoint k s
  disjoint k v
  disjoint K k
  disjoint s v
  disjoint K s
  disjoint K v
  disjoint f k
  disjoint f s
  disjoint f v
  disjoint f x
  disjoint R f
  disjoint k x
  disjoint R k
  disjoint s x
  disjoint R s
  disjoint v x
  disjoint R v
  disjoint R x
  disjoint S f
  disjoint S k
  disjoint S s
  disjoint S v
  disjoint S x
  disjoint T s
  disjoint X k
  disjoint X x
  disjoint f r
  disjoint k r
  disjoint r s
  disjoint r v
  disjoint r x
  disjoint R r
  disjoint S r
  disjoint T r
  assert |- ran T = { s | E. k e. ~P X E. v e. S ( ( R |`t k ) e. Comp /\ s = { f e. ( R Cn S ) | ( f " k ) C_ v } ) }

  proof
    cT
    crn
    vs
    cv
    vf
    cv
    vk
    cv
    #
    cima
    vv
    cv
    wss
    vf
    cR
    cS
    ccn
    co
    crab
    #
    wceq
    #
    vv
    cS
    wrex
    #
    vk
    cK
    wrex
    #
    vs
    cab
    cR
    @0
    crest
    co
    #
    ccmp
    wcel
    #
    @2
    wa
    vv
    cS
    wrex
    #
    vk
    cX
    cpw
    #
    wrex
    #
    vs
    cab
    vk
    vv
    vs
    cK
    cS
    @1
    cT
    xkoval.t
    rnmpt2
    @4
    @9
    vs
    @3
    vk
    cR
    vx
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    vx
    @8
    crab
    #
    wrex
    @6
    @3
    wa
    #
    vk
    @8
    wrex
    @4
    @9
    @12
    @6
    @3
    vk
    vx
    @8
    @10
    @0
    wceq
    @11
    @5
    ccmp
    @10
    @0
    cR
    crest
    oveq2
    eleq1d
    rexrab
    @3
    vk
    cK
    @13
    xkoval.k
    rexeqi
    @7
    @14
    vk
    @8
    @6
    @2
    vv
    cS
    r19.42v
    rexbii
    3bitr4i
    abbii
    eqtri
end
