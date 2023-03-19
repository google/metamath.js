include "cr.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "resqcl.mm"
include "ax-mp.mm"

theorem resqcli
  let cA: class A
  assume resqcl.1: |- A e. RR


  assert |- ( A ^ 2 ) e. RR

  proof
    cA
    cr
    wcel
    cA
    c2
    cexp
    co
    cr
    wcel
    resqcl.1
    cA
    resqcl
    ax-mp
end
