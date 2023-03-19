include "cs4.mm"
include "cs5.mm"
include "df-s5.mm"
include "s4cli.mm"
include "cats1cli.mm"

theorem s5cli
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E


  assert |- <" A B C D E "> e. Word _V

  proof
    cA
    cB
    cC
    cD
    cs4
    cA
    cB
    cC
    cD
    cE
    cs5
    cE
    cA
    cB
    cC
    cD
    cE
    df-s5
    cA
    cB
    cC
    cD
    s4cli
    cats1cli
end
