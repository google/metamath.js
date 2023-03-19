include "cr.mm"
include "wcel.mm"
include "c2.mm"
include "cn0.mm"
include "cexp.mm"
include "co.mm"
include "2nn0.mm"
include "reexpcl.mm"
include "mpan2.mm"

theorem resqcl
  let cA: class A


  assert |- ( A e. RR -> ( A ^ 2 ) e. RR )

  proof
    cA
    cr
    wcel
    c2
    cn0
    wcel
    cA
    c2
    cexp
    co
    cr
    wcel
    2nn0
    cA
    c2
    reexpcl
    mpan2
end
