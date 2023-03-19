include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cn.mm"
include "cexp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "2nn.mm"
include "expeq0.mm"
include "mpan2.mm"

theorem sqeq0
  let cA: class A


  assert |- ( A e. CC -> ( ( A ^ 2 ) = 0 <-> A = 0 ) )

  proof
    cA
    cc
    wcel
    c2
    cn
    wcel
    cA
    c2
    cexp
    co
    cc0
    wceq
    cA
    cc0
    wceq
    wb
    2nn
    cA
    c2
    expeq0
    mpan2
end
