include "cs6.mm"
include "cs7.mm"
include "c6.mm"
include "c7.mm"
include "df-s7.mm"
include "s6cli.mm"
include "s6len.mm"
include "6p1e7.mm"
include "cats1len.mm"

theorem s7len
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G


  assert |- ( # ` <" A B C D E F G "> ) = 7

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
    c6
    c7
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
    cA
    cB
    cC
    cD
    cE
    cF
    s6len
    6p1e7
    cats1len
end
