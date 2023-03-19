include "cs5.mm"
include "cs6.mm"
include "df-s6.mm"
include "s5cli.mm"
include "cats1cli.mm"

theorem s6cli
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F


  assert |- <" A B C D E F "> e. Word _V

  proof
    cA
    cB
    cC
    cD
    cE
    cs5
    cA
    cB
    cC
    cD
    cE
    cF
    cs6
    cF
    cA
    cB
    cC
    cD
    cE
    cF
    df-s6
    cA
    cB
    cC
    cD
    cE
    s5cli
    cats1cli
end
