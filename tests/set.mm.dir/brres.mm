include "cvv.mm"
include "wcel.mm"
include "cres.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "brresg.mm"
include "ax-mp.mm"

theorem brres
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opelres.1: |- B e. _V


  assert |- ( A ( C |` D ) B <-> ( A C B /\ A e. D ) )

  proof
    cB
    cvv
    wcel
    cA
    cB
    cC
    cD
    cres
    wbr
    cA
    cB
    cC
    wbr
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
    brresg
    ax-mp
end
