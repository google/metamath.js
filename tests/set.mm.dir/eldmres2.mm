include "wcel.mm"
include "cres.mm"
include "cdm.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "wa.mm"
include "cec.mm"
include "eldmres.mm"
include "eldmg.mm"
include "eldm4.mm"
include "bitr3d.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem eldmres2
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V

  disjoint A y
  disjoint B y
  disjoint R y
  disjoint V y
  assert |- ( B e. V -> ( B e. dom ( R |` A ) <-> ( B e. A /\ E. y y e. [ B ] R ) ) )

  proof
    cB
    cV
    wcel
    #
    cB
    cR
    cA
    cres
    cdm
    wcel
    cB
    cA
    wcel
    #
    cB
    vy
    cv
    #
    cR
    wbr
    vy
    wex
    #
    wa
    @1
    @2
    cB
    cR
    cec
    wcel
    vy
    wex
    #
    wa
    vy
    cA
    cB
    cR
    cV
    eldmres
    @0
    @3
    @4
    @1
    @0
    cB
    cR
    cdm
    wcel
    @3
    @4
    vy
    cB
    cR
    cV
    eldmg
    vy
    cB
    cR
    cV
    eldm4
    bitr3d
    anbi2d
    bitrd
end
