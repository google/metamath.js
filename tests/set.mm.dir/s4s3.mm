include "cs4.mm"
include "cs6.mm"
include "cs7.mm"
include "cs2.mm"
include "cs3.mm"
include "df-s3.mm"
include "s4cli.mm"
include "s2cli.mm"
include "df-s7.mm"
include "s4s2.mm"
include "cats1cat.mm"

theorem s4s3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G


  assert |- <" A B C D E F G "> = ( <" A B C D "> ++ <" E F G "> )

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
    cE
    cF
    cs2
    cE
    cF
    cG
    cs3
    cG
    cE
    cF
    cG
    df-s3
    cA
    cB
    cC
    cD
    s4cli
    cE
    cF
    s2cli
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
    s4s2
    cats1cat
end
