include "cop.mm"
include "wcel.mm"
include "wbr.mm"
include "crn.mm"
include "df-br.mm"
include "brelrn.mm"
include "sylbir.mm"

theorem opelrn
  let cA: class A
  let cB: class B
  let cC: class C
  assume brelrn.1: |- A e. _V
  assume brelrn.2: |- B e. _V


  assert |- ( <. A , B >. e. C -> B e. ran C )

  proof
    cA
    cB
    cop
    cC
    wcel
    cA
    cB
    cC
    wbr
    cB
    cC
    crn
    wcel
    cA
    cB
    cC
    df-br
    cA
    cB
    cC
    brelrn.1
    brelrn.2
    brelrn
    sylbir
end
