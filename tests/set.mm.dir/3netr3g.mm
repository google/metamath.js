include "wne.mm"
include "neeq12i.mm"
include "sylib.mm"

theorem 3netr3g
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3netr3g.1: |- ( ph -> A =/= B )
  assume 3netr3g.2: |- A = C
  assume 3netr3g.3: |- B = D


  assert |- ( ph -> C =/= D )

  proof
    wph
    cA
    cB
    wne
    cC
    cD
    wne
    3netr3g.1
    cA
    cC
    cB
    cD
    3netr3g.2
    3netr3g.3
    neeq12i
    sylib
end
