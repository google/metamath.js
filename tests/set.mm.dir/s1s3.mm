include "cs1.mm"
include "cs3.mm"
include "cs4.mm"
include "cs2.mm"
include "df-s3.mm"
include "s1cli.mm"
include "s2cli.mm"
include "df-s4.mm"
include "s1s2.mm"
include "cats1cat.mm"

theorem s1s3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- <" A B C D "> = ( <" A "> ++ <" B C D "> )

  proof
    cA
    cs1
    cA
    cB
    cC
    cs3
    cA
    cB
    cC
    cD
    cs4
    cB
    cC
    cs2
    cB
    cC
    cD
    cs3
    cD
    cB
    cC
    cD
    df-s3
    cA
    s1cli
    cB
    cC
    s2cli
    cA
    cB
    cC
    cD
    df-s4
    cA
    cB
    cC
    s1s2
    cats1cat
end
