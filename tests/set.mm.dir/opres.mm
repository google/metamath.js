include "cop.mm"
include "cres.mm"
include "wcel.mm"
include "opelres.mm"
include "rbaib.mm"

theorem opres
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opres.1: |- B e. _V


  assert |- ( A e. D -> ( <. A , B >. e. ( C |` D ) <-> <. A , B >. e. C ) )

  proof
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
    cA
    cB
    cC
    cD
    opres.1
    opelres
    rbaib
end
