include "eqnetrd.mm"
include "neeqtrrd.mm"

theorem 3netr4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3netr4d.1: |- ( ph -> A =/= B )
  assume 3netr4d.2: |- ( ph -> C = A )
  assume 3netr4d.3: |- ( ph -> D = B )


  assert |- ( ph -> C =/= D )

  proof
    wph
    cC
    cB
    cD
    wph
    cC
    cA
    cB
    3netr4d.2
    3netr4d.1
    eqnetrd
    3netr4d.3
    neeqtrrd
end
