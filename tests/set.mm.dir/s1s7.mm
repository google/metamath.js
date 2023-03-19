include "cs1.mm"
include "cs7.mm"
include "cs8.mm"
include "cs6.mm"
include "df-s7.mm"
include "s1cli.mm"
include "s6cli.mm"
include "df-s8.mm"
include "s1s6.mm"
include "cats1cat.mm"

theorem s1s7
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H


  assert |- <" A B C D E F G H "> = ( <" A "> ++ <" B C D E F G H "> )

  proof
    cA
    cs1
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    cs7
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    cH
    cs8
    cB
    cC
    cD
    cE
    cF
    cG
    cs6
    cB
    cC
    cD
    cE
    cF
    cG
    cH
    cs7
    cH
    cB
    cC
    cD
    cE
    cF
    cG
    cH
    df-s7
    cA
    s1cli
    cB
    cC
    cD
    cE
    cF
    cG
    s6cli
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    cH
    df-s8
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    s1s6
    cats1cat
end
