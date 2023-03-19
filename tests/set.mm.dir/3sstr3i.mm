include "wss.mm"
include "sseq12i.mm"
include "mpbi.mm"

theorem 3sstr3i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3sstr3.1: |- A C_ B
  assume 3sstr3.2: |- A = C
  assume 3sstr3.3: |- B = D


  assert |- C C_ D

  proof
    cA
    cB
    wss
    cC
    cD
    wss
    3sstr3.1
    cA
    cC
    cB
    cD
    3sstr3.2
    3sstr3.3
    sseq12i
    mpbi
end
