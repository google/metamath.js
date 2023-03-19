include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "id.mm"
include "wb.mm"
include "eqeq2.mm"
include "adantl.mm"
include "eqidd.mm"
include "rspcedvd.mm"
include "eleq1a.mm"
include "rexlimiv.mm"
include "impbii.mm"

theorem clel5
  let vx: setvar x
  let cA: class A
  let cX: class X

  disjoint A x
  disjoint X x
  assert |- ( X e. A <-> E. x e. A X = x )

  proof
    cX
    cA
    wcel
    #
    cX
    vx
    cv
    #
    wceq
    #
    vx
    cA
    wrex
    @0
    @2
    cX
    cX
    wceq
    #
    vx
    cX
    cA
    @0
    id
    @1
    cX
    wceq
    @2
    @3
    wb
    @0
    @1
    cX
    cX
    eqeq2
    adantl
    @0
    cX
    eqidd
    rspcedvd
    @2
    @0
    vx
    cA
    @1
    cA
    cX
    eleq1a
    rexlimiv
    impbii
end
