include "cs5.mm"
include "cs6.mm"
include "c5.mm"
include "c6.mm"
include "df-s6.mm"
include "s5cli.mm"
include "s5len.mm"
include "5p1e6.mm"
include "cats1len.mm"

theorem s6len
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F


  assert |- ( # ` <" A B C D E F "> ) = 6

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
    c5
    c6
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
    cA
    cB
    cC
    cD
    cE
    s5len
    5p1e6
    cats1len
end
