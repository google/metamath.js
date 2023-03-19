include "wss.mm"
include "sseq12i.mm"
include "mpbir.mm"

theorem 3sstr4i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3sstr4.1: |- A C_ B
  assume 3sstr4.2: |- C = A
  assume 3sstr4.3: |- D = B


  assert |- C C_ D

  proof
    cC
    cD
    wss
    cA
    cB
    wss
    3sstr4.1
    cC
    cA
    cD
    cB
    3sstr4.2
    3sstr4.3
    sseq12i
    mpbir
end
