include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "cgcd.mm"
include "co.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "wb.mm"
include "nnz.mm"
include "gcdzeq.mm"
include "sylan2.mm"

theorem gcdeq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN /\ B e. NN ) -> ( ( A gcd B ) = A <-> A || B ) )

  proof
    cB
    cn
    wcel
    cA
    cn
    wcel
    cB
    cz
    wcel
    cA
    cB
    cgcd
    co
    cA
    wceq
    cA
    cB
    cdvds
    wbr
    wb
    cB
    nnz
    cA
    cB
    gcdzeq
    sylan2
end
