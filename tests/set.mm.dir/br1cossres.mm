include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "ccoss.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "wrex.mm"
include "brcoss.mm"
include "exanres.mm"
include "bitrd.mm"

theorem br1cossres
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cV: class V
  let cW: class W

  disjoint A u
  disjoint B u
  disjoint C u
  disjoint R u
  disjoint V u
  disjoint W u
  assert |- ( ( B e. V /\ C e. W ) -> ( B ,~ ( R |` A ) C <-> E. u e. A ( u R B /\ u R C ) ) )

  proof
    cB
    cV
    wcel
    cC
    cW
    wcel
    wa
    cB
    cC
    cR
    cA
    cres
    #
    ccoss
    wbr
    vu
    cv
    #
    cB
    @0
    wbr
    @1
    cC
    @0
    wbr
    wa
    vu
    wex
    @1
    cB
    cR
    wbr
    @1
    cC
    cR
    wbr
    wa
    vu
    cA
    wrex
    vu
    cB
    cC
    @0
    cV
    cW
    brcoss
    vu
    cA
    cB
    cC
    cR
    cR
    cV
    cW
    exanres
    bitrd
end
