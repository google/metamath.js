include "cs3.mm"
include "cs4.mm"
include "c3.mm"
include "c1.mm"
include "df-s4.mm"
include "s3cli.mm"
include "s3len.mm"
include "s3fv1.mm"
include "1nn0.mm"
include "1lt3.mm"
include "cats1fv.mm"

theorem s4fv1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V


  assert |- ( B e. V -> ( <" A B C D "> ` 1 ) = B )

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
    c1
    cV
    cD
    cB
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
    cA
    cB
    cC
    cV
    s3fv1
    1nn0
    1lt3
    cats1fv
end
