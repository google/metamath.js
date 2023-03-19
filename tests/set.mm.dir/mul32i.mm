include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mul32.mm"
include "mp3an.mm"

theorem mul32i
  let cA: class A
  let cB: class B
  let cC: class C
  assume mul.1: |- A e. CC
  assume mul.2: |- B e. CC
  assume mul.3: |- C e. CC


  assert |- ( ( A x. B ) x. C ) = ( ( A x. C ) x. B )

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
    cmul
    co
    cC
    cmul
    co
    cA
    cC
    cmul
    co
    cB
    cmul
    co
    wceq
    mul.1
    mul.2
    mul.3
    cA
    cB
    cC
    mul32
    mp3an
end
