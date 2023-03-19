include "cs1.mm"
include "cs6.mm"
include "cs7.mm"
include "cs5.mm"
include "df-s6.mm"
include "s1cli.mm"
include "s5cli.mm"
include "df-s7.mm"
include "s1s5.mm"
include "cats1cat.mm"

theorem s1s6
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G


  assert |- <" A B C D E F G "> = ( <" A "> ++ <" B C D E F G "> )

  proof
    cA
    cs1
    cA
    cB
    cC
    cD
    cE
    cF
    cs6
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    cs7
    cB
    cC
    cD
    cE
    cF
    cs5
    cB
    cC
    cD
    cE
    cF
    cG
    cs6
    cG
    cB
    cC
    cD
    cE
    cF
    cG
    df-s6
    cA
    s1cli
    cB
    cC
    cD
    cE
    cF
    s5cli
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    df-s7
    cA
    cB
    cC
    cD
    cE
    cF
    s1s5
    cats1cat
end
