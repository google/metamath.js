include "cs1.mm"
include "cs5.mm"
include "cs6.mm"
include "cs4.mm"
include "df-s5.mm"
include "s1cli.mm"
include "s4cli.mm"
include "df-s6.mm"
include "s1s4.mm"
include "cats1cat.mm"

theorem s1s5
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F


  assert |- <" A B C D E F "> = ( <" A "> ++ <" B C D E F "> )

  proof
    cA
    cs1
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
    cB
    cC
    cD
    cE
    cs4
    cB
    cC
    cD
    cE
    cF
    cs5
    cF
    cB
    cC
    cD
    cE
    cF
    df-s5
    cA
    s1cli
    cB
    cC
    cD
    cE
    s4cli
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
    s1s4
    cats1cat
end
