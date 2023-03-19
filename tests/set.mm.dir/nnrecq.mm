include "c1.mm"
include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "cdiv.mm"
include "co.mm"
include "cq.mm"
include "1z.mm"
include "znq.mm"
include "mpan.mm"

theorem nnrecq
  let cA: class A


  assert |- ( A e. NN -> ( 1 / A ) e. QQ )

  proof
    c1
    cz
    wcel
    cA
    cn
    wcel
    c1
    cA
    cdiv
    co
    cq
    wcel
    1z
    c1
    cA
    znq
    mpan
end
