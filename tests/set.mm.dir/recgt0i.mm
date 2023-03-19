include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "recgt0.mm"
include "mpan.mm"

theorem recgt0i
  let cA: class A
  assume ltplus1.1: |- A e. RR


  assert |- ( 0 < A -> 0 < ( 1 / A ) )

  proof
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    cc0
    c1
    cA
    cdiv
    co
    clt
    wbr
    ltplus1.1
    cA
    recgt0
    mpan
end
