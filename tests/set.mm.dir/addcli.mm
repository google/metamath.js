include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "addcl.mm"
include "mp2an.mm"

theorem addcli
  let cA: class A
  let cB: class B
  assume axi.1: |- A e. CC
  assume axi.2: |- B e. CC


  assert |- ( A + B ) e. CC

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    caddc
    co
    cc
    wcel
    axi.1
    axi.2
    cA
    cB
    addcl
    mp2an
end
