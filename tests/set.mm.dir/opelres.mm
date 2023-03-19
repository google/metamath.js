include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "cres.mm"
include "wa.mm"
include "wb.mm"
include "opelresg.mm"
include "ax-mp.mm"

theorem opelres
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opelres.1: |- B e. _V


  assert |- ( <. A , B >. e. ( C |` D ) <-> ( <. A , B >. e. C /\ A e. D ) )

  proof
    cB
    cvv
    wcel
    cA
    cB
    cop
    #
    cC
    cD
    cres
    wcel
    @0
    cC
    wcel
    cA
    cD
    wcel
    wa
    wb
    opelres.1
    cA
    cB
    cC
    cD
    cvv
    opelresg
    ax-mp
end
