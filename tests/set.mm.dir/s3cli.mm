include "cs2.mm"
include "cs3.mm"
include "df-s3.mm"
include "s2cli.mm"
include "cats1cli.mm"

theorem s3cli
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- <" A B C "> e. Word _V

  proof
    cA
    cB
    cs2
    cA
    cB
    cC
    cs3
    cC
    cA
    cB
    cC
    df-s3
    cA
    cB
    s2cli
    cats1cli
end
