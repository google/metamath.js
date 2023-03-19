include "cn.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "nnmulcl.mm"
include "mp2an.mm"

theorem nnmulcli
  let cA: class A
  let cB: class B
  assume nnmulcli.1: |- A e. NN
  assume nnmulcli.2: |- B e. NN


  assert |- ( A x. B ) e. NN

  proof
    cA
    cn
    wcel
    cB
    cn
    wcel
    cA
    cB
    cmul
    co
    cn
    wcel
    nnmulcli.1
    nnmulcli.2
    cA
    cB
    nnmulcl
    mp2an
end
