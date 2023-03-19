include "cdit.mm"
include "cle.mm"
include "wbr.mm"
include "cioo.mm"
include "co.mm"
include "citg.mm"
include "cneg.mm"
include "cif.mm"
include "cvv.mm"
include "df-ditg.mm"
include "itgex.mm"
include "negex.mm"
include "ifex.mm"
include "eqeltri.mm"

theorem ditgex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- S_ [ A -> B ] C _d x e. _V

  proof
    vx
    cA
    cB
    cC
    cdit
    cA
    cB
    cle
    wbr
    #
    vx
    cA
    cB
    cioo
    co
    #
    cC
    citg
    #
    vx
    cB
    cA
    cioo
    co
    cC
    citg
    #
    cneg
    #
    cif
    cvv
    vx
    cA
    cB
    cC
    df-ditg
    @0
    @2
    @4
    vx
    @1
    cC
    itgex
    @3
    negex
    ifex
    eqeltri
end
