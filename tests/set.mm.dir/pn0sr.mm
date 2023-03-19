include "cnr.mm"
include "wcel.mm"
include "c1r.mm"
include "cmr.mm"
include "co.mm"
include "cm1r.mm"
include "cplr.mm"
include "c0r.mm"
include "1idsr.mm"
include "oveq1d.mm"
include "distrsr.mm"
include "m1p1sr.mm"
include "oveq2i.mm"
include "addcomsr.mm"
include "3eqtr3i.mm"
include "00sr.mm"
include "syl5eqr.mm"
include "eqtr3d.mm"

theorem pn0sr
  let cA: class A


  assert |- ( A e. R. -> ( A +R ( A .R -1R ) ) = 0R )

  proof
    cA
    cnr
    wcel
    #
    cA
    c1r
    cmr
    co
    #
    cA
    cm1r
    cmr
    co
    #
    cplr
    co
    #
    cA
    @2
    cplr
    co
    c0r
    @0
    @1
    cA
    @2
    cplr
    cA
    1idsr
    oveq1d
    @0
    @3
    cA
    c0r
    cmr
    co
    #
    c0r
    cA
    cm1r
    c1r
    cplr
    co
    #
    cmr
    co
    @2
    @1
    cplr
    co
    @4
    @3
    cA
    cm1r
    c1r
    distrsr
    @5
    c0r
    cA
    cmr
    m1p1sr
    oveq2i
    @2
    @1
    addcomsr
    3eqtr3i
    cA
    00sr
    syl5eqr
    eqtr3d
end
