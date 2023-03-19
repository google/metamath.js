include "cop.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cpr.mm"
include "c0.mm"
include "cif.mm"
include "dfopif.mm"
include "prex.mm"
include "0ex.mm"
include "ifex.mm"
include "eqeltri.mm"

theorem opex
  let cA: class A
  let cB: class B


  assert |- <. A , B >. e. _V

  proof
    cA
    cB
    cop
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    #
    cA
    csn
    #
    cA
    cB
    cpr
    #
    cpr
    #
    c0
    cif
    cvv
    cA
    cB
    dfopif
    @0
    @3
    c0
    @1
    @2
    prex
    0ex
    ifex
    eqeltri
end
