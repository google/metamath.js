include "wceq.mm"
include "cpnf.mm"
include "cmnf.mm"
include "cneg.mm"
include "cif.mm"
include "cxne.mm"
include "eqeq1.mm"
include "negeq.mm"
include "ifbieq2d.mm"
include "df-xneg.mm"
include "3eqtr4g.mm"

theorem xnegeq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> -e A = -e B )

  proof
    cA
    cB
    wceq
    #
    cA
    cpnf
    wceq
    #
    cmnf
    cA
    cmnf
    wceq
    #
    cpnf
    cA
    cneg
    #
    cif
    #
    cif
    cB
    cpnf
    wceq
    #
    cmnf
    cB
    cmnf
    wceq
    #
    cpnf
    cB
    cneg
    #
    cif
    #
    cif
    cA
    cxne
    cB
    cxne
    @0
    @1
    @5
    @4
    @8
    cmnf
    cA
    cB
    cpnf
    eqeq1
    @0
    @2
    @6
    @3
    @7
    cpnf
    cA
    cB
    cmnf
    eqeq1
    cA
    cB
    negeq
    ifbieq2d
    ifbieq2d
    cA
    df-xneg
    cB
    df-xneg
    3eqtr4g
end
