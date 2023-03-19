include "cv.mm"
include "wbr.mm"
include "cep.mm"
include "wa.mm"
include "wex.mm"
include "wcel.mm"
include "ccom.mm"
include "wrex.mm"
include "epelc.mm"
include "anbi2i.mm"
include "ancom.mm"
include "bitri.mm"
include "exbii.mm"
include "brco.mm"
include "df-rex.mm"
include "3bitr4i.mm"

theorem coep
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  assume coep.1: |- A e. _V
  assume coep.2: |- B e. _V

  disjoint A x
  disjoint B x
  disjoint R x
  assert |- ( A ( _E o. R ) B <-> E. x e. B A R x )

  proof
    cA
    vx
    cv
    #
    cR
    wbr
    #
    @0
    cB
    cep
    wbr
    #
    wa
    #
    vx
    wex
    @0
    cB
    wcel
    #
    @1
    wa
    #
    vx
    wex
    cA
    cB
    cep
    cR
    ccom
    wbr
    @1
    vx
    cB
    wrex
    @3
    @5
    vx
    @3
    @1
    @4
    wa
    @5
    @2
    @4
    @1
    @0
    cB
    coep.2
    epelc
    anbi2i
    @1
    @4
    ancom
    bitri
    exbii
    vx
    cA
    cB
    cep
    cR
    coep.1
    coep.2
    brco
    @1
    vx
    cB
    df-rex
    3bitr4i
end
