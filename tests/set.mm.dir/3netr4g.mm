include "wne.mm"
include "neeq12i.mm"
include "sylibr.mm"

theorem 3netr4g
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3netr4g.1: |- ( ph -> A =/= B )
  assume 3netr4g.2: |- C = A
  assume 3netr4g.3: |- D = B


  assert |- ( ph -> C =/= D )

  proof
    wph
    cA
    cB
    wne
    cC
    cD
    wne
    3netr4g.1
    cC
    cA
    cD
    cB
    3netr4g.2
    3netr4g.3
    neeq12i
    sylibr
end
