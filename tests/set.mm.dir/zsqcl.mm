include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cn0.mm"
include "cexp.mm"
include "co.mm"
include "2nn0.mm"
include "zexpcl.mm"
include "mpan2.mm"

theorem zsqcl
  let cA: class A


  assert |- ( A e. ZZ -> ( A ^ 2 ) e. ZZ )

  proof
    cA
    cz
    wcel
    c2
    cn0
    wcel
    cA
    c2
    cexp
    co
    cz
    wcel
    2nn0
    cA
    c2
    zexpcl
    mpan2
end
