include "cop.mm"
include "ccom.mm"
include "wcel.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "df-br.mm"
include "brco.mm"
include "bitr3i.mm"

theorem opelco
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opelco.1: |- A e. _V
  assume opelco.2: |- B e. _V

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  assert |- ( <. A , B >. e. ( C o. D ) <-> E. x ( A D x /\ x C B ) )

  proof
    cA
    cB
    cop
    cC
    cD
    ccom
    #
    wcel
    cA
    cB
    @0
    wbr
    cA
    vx
    cv
    #
    cD
    wbr
    @1
    cB
    cC
    wbr
    wa
    vx
    wex
    cA
    cB
    @0
    df-br
    vx
    cA
    cB
    cC
    cD
    opelco.1
    opelco.2
    brco
    bitr3i
end
