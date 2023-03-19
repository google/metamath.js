include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "msqge0.mm"
include "ax-mp.mm"

theorem msqge0i
  let cA: class A
  assume lt2.1: |- A e. RR


  assert |- 0 <_ ( A x. A )

  proof
    cA
    cr
    wcel
    cc0
    cA
    cA
    cmul
    co
    cle
    wbr
    lt2.1
    cA
    msqge0
    ax-mp
end
