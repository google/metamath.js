include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "mulcl.mm"
include "mp2an.mm"

theorem mulcli
  let cA: class A
  let cB: class B
  assume axi.1: |- A e. CC
  assume axi.2: |- B e. CC


  assert |- ( A x. B ) e. CC

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    cmul
    co
    cc
    wcel
    axi.1
    axi.2
    cA
    cB
    mulcl
    mp2an
end
