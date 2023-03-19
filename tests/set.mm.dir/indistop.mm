include "c0.mm"
include "cid.mm"
include "cfv.mm"
include "cpr.mm"
include "ctop.mm"
include "indislem.mm"
include "cvv.mm"
include "wcel.mm"
include "ctopon.mm"
include "fvex.mm"
include "indistopon.mm"
include "ax-mp.mm"
include "topontopi.mm"
include "eqeltrri.mm"

theorem indistop
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cV: class V


  assert |- { (/) , A } e. Top

  proof
    c0
    cA
    cid
    cfv
    #
    cpr
    #
    c0
    cA
    cpr
    ctop
    cA
    indislem
    @0
    @1
    @0
    cvv
    wcel
    @1
    @0
    ctopon
    cfv
    wcel
    cA
    cid
    fvex
    @0
    cvv
    indistopon
    ax-mp
    topontopi
    eqeltrri
end
