include "cs2.mm"
include "cs3.mm"
include "cs4.mm"
include "cs1.mm"
include "df-s2.mm"
include "s2cli.mm"
include "s1cli.mm"
include "df-s4.mm"
include "df-s3.mm"
include "cats1cat.mm"

theorem s2s2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- <" A B C D "> = ( <" A B "> ++ <" C D "> )

  proof
    cA
    cB
    cs2
    cA
    cB
    cC
    cs3
    cA
    cB
    cC
    cD
    cs4
    cC
    cs1
    cC
    cD
    cs2
    cD
    cC
    cD
    df-s2
    cA
    cB
    s2cli
    cC
    s1cli
    cA
    cB
    cC
    cD
    df-s4
    cA
    cB
    cC
    df-s3
    cats1cat
end
