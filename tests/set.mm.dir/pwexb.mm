include "cvv.mm"
include "wcel.mm"
include "cpw.mm"
include "pwexg.mm"
include "pwexr.mm"
include "impbii.mm"

theorem pwexb
  let cA: class A


  assert |- ( A e. _V <-> ~P A e. _V )

  proof
    cA
    cvv
    wcel
    cA
    cpw
    cvv
    wcel
    cA
    cvv
    pwexg
    cA
    cvv
    pwexr
    impbii
end
