include "wss.mm"
include "sseq12i.mm"
include "sylib.mm"

theorem 3sstr3g
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3sstr3g.1: |- ( ph -> A C_ B )
  assume 3sstr3g.2: |- A = C
  assume 3sstr3g.3: |- B = D


  assert |- ( ph -> C C_ D )

  proof
    wph
    cA
    cB
    wss
    cC
    cD
    wss
    3sstr3g.1
    cA
    cC
    cB
    cD
    3sstr3g.2
    3sstr3g.3
    sseq12i
    sylib
end
