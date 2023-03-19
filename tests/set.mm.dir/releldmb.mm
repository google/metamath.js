include "wrel.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "eldmg.mm"
include "ibi.mm"
include "releldm.mm"
include "ex.mm"
include "exlimdv.mm"
include "impbid2.mm"

theorem releldmb
  let vx: setvar x
  let cA: class A
  let cR: class R

  disjoint A x
  disjoint R x
  assert |- ( Rel R -> ( A e. dom R <-> E. x A R x ) )

  proof
    cR
    wrel
    #
    cA
    cR
    cdm
    #
    wcel
    #
    cA
    vx
    cv
    #
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
    eldmg
    ibi
    @0
    @4
    @2
    vx
    @0
    @4
    @2
    cA
    @3
    cR
    releldm
    ex
    exlimdv
    impbid2
end
