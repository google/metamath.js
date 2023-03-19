include "wcel.mm"
include "cop.mm"
include "cres.mm"
include "wa.mm"
include "wbr.mm"
include "opelresg.mm"
include "df-br.mm"
include "anbi1i.mm"
include "3bitr4g.mm"

theorem brresg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V


  assert |- ( B e. V -> ( A ( C |` D ) B <-> ( A C B /\ A e. D ) ) )

  proof
    cB
    cV
    wcel
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
    cV
    opelresg
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
    3bitr4g
end
