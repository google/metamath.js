include "cs4.mm"
include "cs5.mm"
include "cs6.mm"
include "cs1.mm"
include "cs2.mm"
include "df-s2.mm"
include "s4cli.mm"
include "s1cli.mm"
include "df-s6.mm"
include "df-s5.mm"
include "cats1cat.mm"

theorem s4s2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F


  assert |- <" A B C D E F "> = ( <" A B C D "> ++ <" E F "> )

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
    cA
    cB
    cC
    cD
    cE
    cF
    cs6
    cE
    cs1
    cE
    cF
    cs2
    cF
    cE
    cF
    df-s2
    cA
    cB
    cC
    cD
    s4cli
    cE
    s1cli
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
    df-s5
    cats1cat
end
