include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "addcan2.mm"
include "mp3an.mm"

theorem addcan2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume mul.1: |- A e. CC
  assume mul.2: |- B e. CC
  assume mul.3: |- C e. CC


  assert |- ( ( A + C ) = ( B + C ) <-> A = B )

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
    cC
    caddc
    co
    cB
    cC
    caddc
    co
    wceq
    cA
    cB
    wceq
    wb
    mul.1
    mul.2
    mul.3
    cA
    cB
    cC
    addcan2
    mp3an
end
