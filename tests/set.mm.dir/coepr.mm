include "cv.mm"
include "cep.mm"
include "ccnv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wcel.mm"
include "ccom.mm"
include "wrex.mm"
include "vex.mm"
include "brcnv.mm"
include "epelc.mm"
include "bitri.mm"
include "anbi1i.mm"
include "exbii.mm"
include "brco.mm"
include "df-rex.mm"
include "3bitr4i.mm"

theorem coepr
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  assume coep.1: |- A e. _V
  assume coep.2: |- B e. _V

  disjoint A x
  disjoint B x
  disjoint R x
  assert |- ( A ( R o. `' _E ) B <-> E. x e. A x R B )

  proof
    cA
    vx
    cv
    #
    cep
    ccnv
    #
    wbr
    #
    @0
    cB
    cR
    wbr
    #
    wa
    #
    vx
    wex
    @0
    cA
    wcel
    #
    @3
    wa
    #
    vx
    wex
    cA
    cB
    cR
    @1
    ccom
    wbr
    @3
    vx
    cA
    wrex
    @4
    @6
    vx
    @2
    @5
    @3
    @2
    @0
    cA
    cep
    wbr
    @5
    cA
    @0
    cep
    coep.1
    vx
    vex
    brcnv
    @0
    cA
    coep.1
    epelc
    bitri
    anbi1i
    exbii
    vx
    cA
    cB
    cR
    @1
    coep.1
    coep.2
    brco
    @3
    vx
    cA
    df-rex
    3bitr4i
end
