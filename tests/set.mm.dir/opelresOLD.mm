include "cop.mm"
include "cres.mm"
include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "wa.mm"
include "df-res.mm"
include "eleq2i.mm"
include "elin.mm"
include "opelxp.mm"
include "mpbiran2.mm"
include "anbi2i.mm"
include "3bitri.mm"

theorem opelresOLD
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opelresOLD.1: |- B e. _V


  assert |- ( <. A , B >. e. ( C |` D ) <-> ( <. A , B >. e. C /\ A e. D ) )

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
    cD
    cvv
    cxp
    #
    cin
    #
    wcel
    @0
    cC
    wcel
    #
    @0
    @2
    wcel
    #
    wa
    @4
    cA
    cD
    wcel
    #
    wa
    @1
    @3
    @0
    cC
    cD
    df-res
    eleq2i
    @0
    cC
    @2
    elin
    @5
    @6
    @4
    @5
    @6
    cB
    cvv
    wcel
    opelresOLD.1
    cA
    cB
    cD
    cvv
    opelxp
    mpbiran2
    anbi2i
    3bitri
end
