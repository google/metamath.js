include "c0.mm"
include "cpr.mm"
include "cuni.mm"
include "cun.mm"
include "0ex.mm"
include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltrri.mm"
include "unipr.mm"
include "uncom.mm"
include "un0.mm"
include "3eqtrri.mm"
include "indistop.mm"
include "istpsi.mm"

theorem indistps2
  let cA: class A
  let cK: class K
  assume indistps2.a: |- ( Base ` K ) = A
  assume indistps2.j: |- ( TopOpen ` K ) = { (/) , A }


  assert |- K e. TopSp

  proof
    cA
    c0
    cA
    cpr
    #
    cK
    indistps2.a
    indistps2.j
    @0
    cuni
    c0
    cA
    cun
    cA
    c0
    cun
    cA
    c0
    cA
    0ex
    cK
    cbs
    cfv
    cA
    cvv
    indistps2.a
    cK
    cbs
    fvex
    eqeltrri
    unipr
    c0
    cA
    uncom
    cA
    un0
    3eqtrri
    cA
    indistop
    istpsi
end
