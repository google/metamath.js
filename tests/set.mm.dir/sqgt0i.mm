include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "sqgt0.mm"
include "mpan.mm"

theorem sqgt0i
  let cA: class A
  assume resqcl.1: |- A e. RR


  assert |- ( A =/= 0 -> 0 < ( A ^ 2 ) )

  proof
    cA
    cr
    wcel
    cA
    cc0
    wne
    cc0
    cA
    c2
    cexp
    co
    clt
    wbr
    resqcl.1
    cA
    sqgt0
    mpan
end
