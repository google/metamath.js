include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "msqgt0.mm"
include "mpan.mm"

theorem msqgt0i
  let cA: class A
  assume lt2.1: |- A e. RR


  assert |- ( A =/= 0 -> 0 < ( A x. A ) )

  proof
    cA
    cr
    wcel
    cA
    cc0
    wne
    cc0
    cA
    cA
    cmul
    co
    clt
    wbr
    lt2.1
    cA
    msqgt0
    mpan
end
