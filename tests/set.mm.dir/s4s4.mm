include "cs4.mm"
include "cs7.mm"
include "cs8.mm"
include "cs3.mm"
include "df-s4.mm"
include "s4cli.mm"
include "s3cli.mm"
include "df-s8.mm"
include "s4s3.mm"
include "cats1cat.mm"

theorem s4s4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H


  assert |- <" A B C D E F G H "> = ( <" A B C D "> ++ <" E F G H "> )

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
    cE
    cF
    cG
    cs3
    cE
    cF
    cG
    cH
    cs4
    cH
    cE
    cF
    cG
    cH
    df-s4
    cA
    cB
    cC
    cD
    s4cli
    cE
    cF
    cG
    s3cli
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
    s4s3
    cats1cat
end
