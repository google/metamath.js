include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "simp2bi.mm"

theorem elunitge0
  let cA: class A


  assert |- ( A e. ( 0 [,] 1 ) -> 0 <_ A )

  proof
    cA
    cc0
    c1
    cicc
    co
    wcel
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cA
    c1
    cle
    wbr
    cc0
    c1
    cA
    0re
    1re
    elicc2i
    simp2bi
end
