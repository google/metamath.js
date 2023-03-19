include "c1.mm"
include "crp.mm"
include "wcel.mm"
include "cdiv.mm"
include "co.mm"
include "1rp.mm"
include "rpdivcl.mm"
include "mpan.mm"

theorem rpreccl
  let cA: class A


  assert |- ( A e. RR+ -> ( 1 / A ) e. RR+ )

  proof
    c1
    crp
    wcel
    cA
    crp
    wcel
    c1
    cA
    cdiv
    co
    crp
    wcel
    1rp
    c1
    cA
    rpdivcl
    mpan
end
