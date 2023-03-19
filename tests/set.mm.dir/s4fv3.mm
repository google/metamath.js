include "cs3.mm"
include "cs4.mm"
include "c3.mm"
include "df-s4.mm"
include "s3cli.mm"
include "s3len.mm"
include "cats1fvn.mm"

theorem s4fv3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V


  assert |- ( D e. V -> ( <" A B C D "> ` 3 ) = D )

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
    c3
    cV
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
    cA
    cB
    cC
    s3len
    cats1fvn
end
