include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wb.mm"
include "nnz.mm"
include "zleltp1.mm"
include "syl2an.mm"

theorem nnleltp1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN /\ B e. NN ) -> ( A <_ B <-> A < ( B + 1 ) ) )

  proof
    cA
    cn
    wcel
    cA
    cz
    wcel
    cB
    cz
    wcel
    cA
    cB
    cle
    wbr
    cA
    cB
    c1
    caddc
    co
    clt
    wbr
    wb
    cB
    cn
    wcel
    cA
    nnz
    cB
    nnz
    cA
    cB
    zleltp1
    syl2an
end
