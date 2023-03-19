include "com.mm"
include "wcel.mm"
include "comu.mm"
include "co.mm"
include "nnmcl.mm"
include "mp2an.mm"

theorem nnmcli
  let cA: class A
  let cB: class B
  assume nncli.1: |- A e. _om
  assume nncli.2: |- B e. _om


  assert |- ( A .o B ) e. _om

  proof
    cA
    com
    wcel
    cB
    com
    wcel
    cA
    cB
    comu
    co
    com
    wcel
    nncli.1
    nncli.2
    cA
    cB
    nnmcl
    mp2an
end
