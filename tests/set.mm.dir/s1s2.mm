include "cs1.mm"
include "cs2.mm"
include "cs3.mm"
include "df-s2.mm"
include "s1cli.mm"
include "df-s3.mm"
include "cats1cat.mm"

theorem s1s2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- <" A B C "> = ( <" A "> ++ <" B C "> )

  proof
    cA
    cs1
    cA
    cB
    cs2
    cA
    cB
    cC
    cs3
    cB
    cs1
    cB
    cC
    cs2
    cC
    cB
    cC
    df-s2
    cA
    s1cli
    cB
    s1cli
    cA
    cB
    cC
    df-s3
    cA
    cB
    df-s2
    cats1cat
end
