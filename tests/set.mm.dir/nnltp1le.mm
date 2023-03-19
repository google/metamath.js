include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wb.mm"
include "nnz.mm"
include "zltp1le.mm"
include "syl2an.mm"

theorem nnltp1le
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN /\ B e. NN ) -> ( A < B <-> ( A + 1 ) <_ B ) )

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
    clt
    wbr
    cA
    c1
    caddc
    co
    cB
    cle
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
    zltp1le
    syl2an
end
