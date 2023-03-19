include "cs7.mm"
include "cs8.mm"
include "df-s8.mm"
include "s7cli.mm"
include "cats1cli.mm"

theorem s8cli
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H


  assert |- <" A B C D E F G H "> e. Word _V

  proof
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
    cH
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
    s7cli
    cats1cli
end
