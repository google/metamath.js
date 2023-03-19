include "cop.mm"
include "cres.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "opelres.mm"
include "df-br.mm"
include "anbi1i.mm"
include "3bitr4i.mm"

theorem brresOLD
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opelresOLD.1: |- B e. _V


  assert |- ( A ( C |` D ) B <-> ( A C B /\ A e. D ) )

  proof
    cA
    cB
    cop
    #
    cC
    cD
    cres
    #
    wcel
    @0
    cC
    wcel
    #
    cA
    cD
    wcel
    #
    wa
    cA
    cB
    @1
    wbr
    cA
    cB
    cC
    wbr
    #
    @3
    wa
    cA
    cB
    cC
    cD
    opelresOLD.1
    opelres
    cA
    cB
    @1
    df-br
    @4
    @2
    @3
    cA
    cB
    cC
    df-br
    anbi1i
    3bitr4i
end
