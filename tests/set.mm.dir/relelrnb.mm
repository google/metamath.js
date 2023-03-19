include "wrel.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "elrng.mm"
include "ibi.mm"
include "relelrn.mm"
include "ex.mm"
include "exlimdv.mm"
include "impbid2.mm"

theorem relelrnb
  let vx: setvar x
  let cA: class A
  let cR: class R

  disjoint A x
  disjoint R x
  assert |- ( Rel R -> ( A e. ran R <-> E. x x R A ) )

  proof
    cR
    wrel
    #
    cA
    cR
    crn
    #
    wcel
    #
    vx
    cv
    #
    cA
    cR
    wbr
    #
    vx
    wex
    #
    @2
    @5
    vx
    cA
    cR
    @1
    elrng
    ibi
    @0
    @4
    @2
    vx
    @0
    @4
    @2
    @3
    cA
    cR
    relelrn
    ex
    exlimdv
    impbid2
end
