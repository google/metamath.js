include "cs1.mm"
include "cs4.mm"
include "cs5.mm"
include "cs3.mm"
include "df-s4.mm"
include "s1cli.mm"
include "s3cli.mm"
include "df-s5.mm"
include "s1s3.mm"
include "cats1cat.mm"

theorem s1s4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E


  assert |- <" A B C D E "> = ( <" A "> ++ <" B C D E "> )

  proof
    cA
    cs1
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
    cB
    cC
    cD
    cs3
    cB
    cC
    cD
    cE
    cs4
    cE
    cB
    cC
    cD
    cE
    df-s4
    cA
    s1cli
    cB
    cC
    cD
    s3cli
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
    s1s3
    cats1cat
end
