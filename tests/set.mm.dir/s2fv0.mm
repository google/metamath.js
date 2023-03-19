include "cs1.mm"
include "cs2.mm"
include "c1.mm"
include "cc0.mm"
include "df-s2.mm"
include "s1cli.mm"
include "s1len.mm"
include "s1fv.mm"
include "0nn0.mm"
include "0lt1.mm"
include "cats1fv.mm"

theorem s2fv0
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( <" A B "> ` 0 ) = A )

  proof
    cA
    cs1
    cA
    cB
    cs2
    c1
    cc0
    cV
    cB
    cA
    cA
    cB
    df-s2
    cA
    s1cli
    cA
    s1len
    cA
    cV
    s1fv
    0nn0
    0lt1
    cats1fv
end
