include "cs7.mm"
include "cs8.mm"
include "c7.mm"
include "c8.mm"
include "df-s8.mm"
include "s7cli.mm"
include "s7len.mm"
include "7p1e8.mm"
include "cats1len.mm"

theorem s8len
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H


  assert |- ( # ` <" A B C D E F G H "> ) = 8

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
    c7
    c8
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
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    s7len
    7p1e8
    cats1len
end
