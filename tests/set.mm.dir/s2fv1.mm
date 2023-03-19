include "cs1.mm"
include "cs2.mm"
include "c1.mm"
include "df-s2.mm"
include "s1cli.mm"
include "s1len.mm"
include "cats1fvn.mm"

theorem s2fv1
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( B e. V -> ( <" A B "> ` 1 ) = B )

  proof
    cA
    cs1
    cA
    cB
    cs2
    c1
    cV
    cB
    cA
    cB
    df-s2
    cA
    s1cli
    cA
    s1len
    cats1fvn
end
