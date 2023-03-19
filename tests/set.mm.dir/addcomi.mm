include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "addcom.mm"
include "mp2an.mm"

theorem addcomi
  let cA: class A
  let cB: class B
  assume mul.1: |- A e. CC
  assume mul.2: |- B e. CC


  assert |- ( A + B ) = ( B + A )

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
    cB
    cA
    caddc
    co
    wceq
    mul.1
    mul.2
    cA
    cB
    addcom
    mp2an
end
