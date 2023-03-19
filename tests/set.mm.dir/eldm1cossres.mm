include "wcel.mm"
include "cres.mm"
include "ccoss.mm"
include "cdm.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "eldmcoss.mm"
include "brresALTV.mm"
include "exbidv.mm"
include "bitrd.mm"
include "df-rex.mm"
include "syl6bbr.mm"

theorem eldm1cossres
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V

  disjoint A u
  disjoint B u
  disjoint R u
  disjoint V u
  assert |- ( B e. V -> ( B e. dom ,~ ( R |` A ) <-> E. u e. A u R B ) )

  proof
    cB
    cV
    wcel
    #
    cB
    cR
    cA
    cres
    #
    ccoss
    cdm
    wcel
    #
    vu
    cv
    #
    cA
    wcel
    @3
    cB
    cR
    wbr
    #
    wa
    #
    vu
    wex
    #
    @4
    vu
    cA
    wrex
    @0
    @2
    @3
    cB
    @1
    wbr
    #
    vu
    wex
    @6
    vu
    cB
    @1
    cV
    eldmcoss
    @0
    @7
    @5
    vu
    cA
    @3
    cB
    cR
    cV
    brresALTV
    exbidv
    bitrd
    @4
    vu
    cA
    df-rex
    syl6bbr
end
