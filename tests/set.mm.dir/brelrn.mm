include "cvv.mm"
include "wcel.mm"
include "wbr.mm"
include "crn.mm"
include "brelrng.mm"
include "mp3an12.mm"

theorem brelrn
  let cA: class A
  let cB: class B
  let cC: class C
  assume brelrn.1: |- A e. _V
  assume brelrn.2: |- B e. _V


  assert |- ( A C B -> B e. ran C )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cC
    wbr
    cB
    cC
    crn
    wcel
    brelrn.1
    brelrn.2
    cA
    cB
    cC
    cvv
    cvv
    brelrng
    mp3an12
end
