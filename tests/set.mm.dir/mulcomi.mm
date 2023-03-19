include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulcom.mm"
include "mp2an.mm"

theorem mulcomi
  let cA: class A
  let cB: class B
  assume axi.1: |- A e. CC
  assume axi.2: |- B e. CC


  assert |- ( A x. B ) = ( B x. A )

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
    cB
    cA
    cmul
    co
    wceq
    axi.1
    axi.2
    cA
    cB
    mulcom
    mp2an
end
