include "cs4.mm"
include "cs5.mm"
include "c4.mm"
include "c5.mm"
include "df-s5.mm"
include "s4cli.mm"
include "s4len.mm"
include "4p1e5.mm"
include "cats1len.mm"

theorem s5len
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E


  assert |- ( # ` <" A B C D E "> ) = 5

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
    c4
    c5
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
    cA
    cB
    cC
    cD
    s4len
    4p1e5
    cats1len
end
