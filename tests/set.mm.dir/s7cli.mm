include "cs6.mm"
include "cs7.mm"
include "df-s7.mm"
include "s6cli.mm"
include "cats1cli.mm"

theorem s7cli
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G


  assert |- <" A B C D E F G "> e. Word _V

  proof
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
    cG
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
    s6cli
    cats1cli
end
