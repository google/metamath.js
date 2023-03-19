include "cs1.mm"
include "cs2.mm"
include "c1.mm"
include "c2.mm"
include "df-s2.mm"
include "s1cli.mm"
include "s1len.mm"
include "1p1e2.mm"
include "cats1len.mm"

theorem s2len
  let cA: class A
  let cB: class B


  assert |- ( # ` <" A B "> ) = 2

  proof
    cA
    cs1
    cA
    cB
    cs2
    c1
    c2
    cB
    cA
    cB
    df-s2
    cA
    s1cli
    cA
    s1len
    1p1e2
    cats1len
end
