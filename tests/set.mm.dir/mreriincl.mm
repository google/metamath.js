include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "ciin.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "riin0.mm"
include "adantl.mm"
include "mre1cl.mm"
include "ad2antrr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "wss.mm"
include "mress.mm"
include "ex.mm"
include "ralimdv.mm"
include "imp.mm"
include "riinn0.mm"
include "sylan.mm"
include "simpll.mm"
include "simpr.mm"
include "simplr.mm"
include "mreiincl.mm"
include "syl3anc.mm"
include "pm2.61dane.mm"

theorem mreriincl
  let vy: setvar y
  let cC: class C
  let cS: class S
  let cI: class I
  let cX: class X
  let vc: setvar c
  let vs: setvar s
  let vx: setvar x

  disjoint I y
  disjoint X y
  disjoint C y
  disjoint C c
  disjoint C s
  disjoint C x
  disjoint c s
  disjoint c x
  disjoint s x
  disjoint X c
  disjoint X s
  disjoint X x
  disjoint S c
  disjoint S s
  disjoint S x
  disjoint I s
  disjoint s y
  assert |- ( ( C e. ( Moore ` X ) /\ A. y e. I S e. C ) -> ( X i^i |^|_ y e. I S ) e. C )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cS
    cC
    wcel
    #
    vy
    cI
    wral
    #
    wa
    #
    cX
    vy
    cI
    cS
    ciin
    #
    cin
    #
    cC
    wcel
    cI
    c0
    @3
    cI
    c0
    wceq
    #
    wa
    @5
    cX
    cC
    @6
    @5
    cX
    wceq
    @3
    vy
    cX
    cS
    cI
    riin0
    adantl
    @0
    cX
    cC
    wcel
    @2
    @6
    cC
    cX
    mre1cl
    ad2antrr
    eqeltrd
    @3
    cI
    c0
    wne
    #
    wa
    #
    @5
    @4
    cC
    @3
    cS
    cX
    wss
    #
    vy
    cI
    wral
    #
    @7
    @5
    @4
    wceq
    @0
    @2
    @10
    @0
    @1
    @9
    vy
    cI
    @0
    @1
    @9
    cC
    cS
    cX
    mress
    ex
    ralimdv
    imp
    vy
    cX
    cS
    cI
    riinn0
    sylan
    @8
    @0
    @7
    @2
    @4
    cC
    wcel
    @0
    @2
    @7
    simpll
    @3
    @7
    simpr
    @0
    @2
    @7
    simplr
    vy
    cC
    cS
    cI
    cX
    mreiincl
    syl3anc
    eqeltrd
    pm2.61dane
end
