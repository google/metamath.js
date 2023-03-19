include "wcel.mm"
include "wa.mm"
include "ccoss.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "cec.mm"
include "brcoss.mm"
include "exan3.mm"
include "bitr4d.mm"

theorem brcoss2
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W

  disjoint A u
  disjoint B u
  disjoint R u
  disjoint V u
  disjoint W u
  assert |- ( ( A e. V /\ B e. W ) -> ( A ,~ R B <-> E. u ( A e. [ u ] R /\ B e. [ u ] R ) ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    cA
    cB
    cR
    ccoss
    wbr
    vu
    cv
    #
    cA
    cR
    wbr
    @0
    cB
    cR
    wbr
    wa
    vu
    wex
    cA
    @0
    cR
    cec
    #
    wcel
    cB
    @1
    wcel
    wa
    vu
    wex
    vu
    cA
    cB
    cR
    cV
    cW
    brcoss
    vu
    cA
    cB
    cR
    cV
    cW
    exan3
    bitr4d
end
