include "wss.mm"
include "sseq12i.mm"
include "sylibr.mm"

theorem 3sstr4g
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3sstr4g.1: |- ( ph -> A C_ B )
  assume 3sstr4g.2: |- C = A
  assume 3sstr4g.3: |- D = B


  assert |- ( ph -> C C_ D )

  proof
    wph
    cA
    cB
    wss
    cC
    cD
    wss
    3sstr4g.1
    cC
    cA
    cD
    cB
    3sstr4g.2
    3sstr4g.3
    sseq12i
    sylibr
end
