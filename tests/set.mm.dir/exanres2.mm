include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cres.mm"
include "wbr.mm"
include "wex.mm"
include "wrex.mm"
include "cec.mm"
include "exanres.mm"
include "exanres3.mm"
include "bitr4d.mm"

theorem exanres2
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W

  disjoint B u
  disjoint C u
  disjoint V u
  disjoint W u
  assert |- ( ( B e. V /\ C e. W ) -> ( E. u ( u ( R |` A ) B /\ u ( S |` A ) C ) <-> E. u e. A ( B e. [ u ] R /\ C e. [ u ] S ) ) )

  proof
    cB
    cV
    wcel
    cC
    cW
    wcel
    wa
    vu
    cv
    #
    cB
    cR
    cA
    cres
    wbr
    @0
    cC
    cS
    cA
    cres
    wbr
    wa
    vu
    wex
    @0
    cB
    cR
    wbr
    @0
    cC
    cS
    wbr
    wa
    vu
    cA
    wrex
    cB
    @0
    cR
    cec
    wcel
    cC
    @0
    cS
    cec
    wcel
    wa
    vu
    cA
    wrex
    vu
    cA
    cB
    cC
    cR
    cS
    cV
    cW
    exanres
    vu
    cA
    cB
    cC
    cR
    cS
    cV
    cW
    exanres3
    bitr4d
end
