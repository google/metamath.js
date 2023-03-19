include "crp.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "2rp.mm"
include "rpdivcl.mm"
include "mpan2.mm"

theorem rphalfcl
  let cA: class A


  assert |- ( A e. RR+ -> ( A / 2 ) e. RR+ )

  proof
    cA
    crp
    wcel
    c2
    crp
    wcel
    cA
    c2
    cdiv
    co
    crp
    wcel
    2rp
    cA
    c2
    rpdivcl
    mpan2
end
