include "cid.mm"
include "cfv.mm"
include "c0.mm"
include "cpr.mm"
include "ctopon.mm"
include "indislem.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "indistopon.mm"
include "ax-mp.mm"
include "eqeltrri.mm"
include "toponunii.mm"

theorem indisuni
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cV: class V


  assert |- ( _I ` A ) = U. { (/) , A }

  proof
    cA
    cid
    cfv
    #
    c0
    cA
    cpr
    #
    c0
    @0
    cpr
    #
    @1
    @0
    ctopon
    cfv
    #
    cA
    indislem
    @0
    cvv
    wcel
    @2
    @3
    wcel
    cA
    cid
    fvex
    @0
    cvv
    indistopon
    ax-mp
    eqeltrri
    toponunii
end
