include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mul4.mm"
include "mp4an.mm"

theorem mul4i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume mul.1: |- A e. CC
  assume mul.2: |- B e. CC
  assume mul.3: |- C e. CC
  assume mul4.4: |- D e. CC


  assert |- ( ( A x. B ) x. ( C x. D ) ) = ( ( A x. C ) x. ( B x. D ) )

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
    cD
    cc
    wcel
    cA
    cB
    cmul
    co
    cC
    cD
    cmul
    co
    cmul
    co
    cA
    cC
    cmul
    co
    cB
    cD
    cmul
    co
    cmul
    co
    wceq
    mul.1
    mul.2
    mul.3
    mul4.4
    cA
    cB
    cC
    cD
    mul4
    mp4an
end
