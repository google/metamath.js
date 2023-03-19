include "cxrn.mm"
include "cxp.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "copab.mm"
include "inxp2.mm"
include "w3a.mm"
include "3ancoma.mm"
include "df-3an.mm"
include "3anass.mm"
include "3bitr3i.mm"
include "opabbii.mm"
include "eqtri.mm"

theorem xrninxp2
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S

  disjoint A u
  disjoint A x
  disjoint u x
  disjoint B u
  disjoint B x
  disjoint C u
  disjoint C x
  disjoint R u
  disjoint R x
  disjoint S u
  disjoint S x
  assert |- ( ( R |X. S ) i^i ( A X. ( B X. C ) ) ) = { <. u , x >. | ( x e. ( B X. C ) /\ ( u e. A /\ u ( R |X. S ) x ) ) }

  proof
    cR
    cS
    cxrn
    #
    cA
    cB
    cC
    cxp
    #
    cxp
    cin
    vu
    cv
    #
    cA
    wcel
    #
    vx
    cv
    #
    @1
    wcel
    #
    wa
    @2
    @4
    @0
    wbr
    #
    wa
    #
    vu
    vx
    copab
    @5
    @3
    @6
    wa
    wa
    #
    vu
    vx
    copab
    vu
    vx
    cA
    @1
    @0
    inxp2
    @7
    @8
    vu
    vx
    @3
    @5
    @6
    w3a
    @5
    @3
    @6
    w3a
    @7
    @8
    @3
    @5
    @6
    3ancoma
    @3
    @5
    @6
    df-3an
    @5
    @3
    @6
    3anass
    3bitr3i
    opabbii
    eqtri
end
