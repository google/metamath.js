include "cfix.mm"
include "ccnv.mm"
include "cv.mm"
include "wbr.mm"
include "wcel.mm"
include "vex.mm"
include "brcnv.mm"
include "elfix.mm"
include "3bitr4ri.mm"
include "eqriv.mm"

theorem fixcnv
  let cA: class A
  let vx: setvar x


  assert |- Fix A = Fix `' A

  proof
    vx
    cA
    cfix
    #
    cA
    ccnv
    #
    cfix
    #
    vx
    cv
    #
    @3
    @1
    wbr
    @3
    @3
    cA
    wbr
    @3
    @2
    wcel
    @3
    @0
    wcel
    @3
    @3
    cA
    vx
    vex
    #
    @4
    brcnv
    @3
    @1
    @4
    elfix
    @3
    cA
    @4
    elfix
    3bitr4ri
    eqriv
end
