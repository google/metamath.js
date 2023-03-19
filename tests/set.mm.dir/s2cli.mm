include "cs1.mm"
include "cs2.mm"
include "df-s2.mm"
include "s1cli.mm"
include "cats1cli.mm"

theorem s2cli
  let cA: class A
  let cB: class B


  assert |- <" A B "> e. Word _V

  proof
    cA
    cs1
    cA
    cB
    cs2
    cB
    cA
    cB
    df-s2
    cA
    s1cli
    cats1cli
end
