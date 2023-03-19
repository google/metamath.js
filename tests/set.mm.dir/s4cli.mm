include "cs3.mm"
include "cs4.mm"
include "df-s4.mm"
include "s3cli.mm"
include "cats1cli.mm"

theorem s4cli
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- <" A B C D "> e. Word _V

  proof
    cA
    cB
    cC
    cs3
    cA
    cB
    cC
    cD
    cs4
    cD
    cA
    cB
    cC
    cD
    df-s4
    cA
    cB
    cC
    s3cli
    cats1cli
end
