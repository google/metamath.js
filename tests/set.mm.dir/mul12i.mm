include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mul12.mm"
include "mp3an.mm"

theorem mul12i
  let cA: class A
  let cB: class B
  let cC: class C
  assume mul.1: |- A e. CC
  assume mul.2: |- B e. CC
  assume mul.3: |- C e. CC


  assert |- ( A x. ( B x. C ) ) = ( B x. ( A x. C ) )

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
    cC
    cmul
    co
    cmul
    co
    cB
    cA
    cC
    cmul
    co
    cmul
    co
    wceq
    mul.1
    mul.2
    mul.3
    cA
    cB
    cC
    mul12
    mp3an
end
