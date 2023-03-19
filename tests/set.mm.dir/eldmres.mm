include "wcel.mm"
include "cres.mm"
include "cdm.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "wa.mm"
include "eldmg.mm"
include "wb.mm"
include "cvv.mm"
include "brresALTV.mm"
include "elv.mm"
include "exbii.mm"
include "19.42v.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem eldmres
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V

  disjoint A y
  disjoint B y
  disjoint R y
  assert |- ( B e. V -> ( B e. dom ( R |` A ) <-> ( B e. A /\ E. y B R y ) ) )

  proof
    cB
    cV
    wcel
    cB
    cR
    cA
    cres
    #
    cdm
    wcel
    cB
    vy
    cv
    #
    @0
    wbr
    #
    vy
    wex
    #
    cB
    cA
    wcel
    #
    cB
    @1
    cR
    wbr
    #
    vy
    wex
    wa
    #
    vy
    cB
    @0
    cV
    eldmg
    @3
    @4
    @5
    wa
    #
    vy
    wex
    @6
    @2
    @7
    vy
    @2
    @7
    wb
    vy
    cA
    cB
    @1
    cR
    cvv
    brresALTV
    elv
    exbii
    @4
    @5
    vy
    19.42v
    bitri
    syl6bb
end
