include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "addcan.mm"
include "mp3an.mm"

theorem addcani
  let cA: class A
  let cB: class B
  let cC: class C
  assume mul.1: |- A e. CC
  assume mul.2: |- B e. CC
  assume mul.3: |- C e. CC


  assert |- ( ( A + B ) = ( A + C ) <-> B = C )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cc
    wcel
    cA
    cB
    caddc
    co
    cA
    cC
    caddc
    co
    wceq
    cB
    cC
    wceq
    wb
    mul.1
    mul.2
    mul.3
    cA
    cB
    cC
    addcan
    mp3an
end
