include "ctps.mm"
include "wcel.mm"
include "c0.mm"
include "cpr.mm"
include "ctopon.mm"
include "cfv.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltrri.mm"
include "indistopon.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "ctopn.mm"
include "istps.mm"
include "mpbir.mm"

theorem indistps2ALT
  let cA: class A
  let cK: class K
  assume indistps2ALT.a: |- ( Base ` K ) = A
  assume indistps2ALT.j: |- ( TopOpen ` K ) = { (/) , A }


  assert |- K e. TopSp

  proof
    cK
    ctps
    wcel
    c0
    cA
    cpr
    #
    cA
    ctopon
    cfv
    wcel
    #
    cA
    cvv
    wcel
    @1
    cK
    cbs
    cfv
    #
    cA
    cvv
    indistps2ALT.a
    cK
    cbs
    fvex
    eqeltrri
    cA
    cvv
    indistopon
    ax-mp
    cA
    @0
    cK
    @2
    cA
    indistps2ALT.a
    eqcomi
    cK
    ctopn
    cfv
    @0
    indistps2ALT.j
    eqcomi
    istps
    mpbir
end
