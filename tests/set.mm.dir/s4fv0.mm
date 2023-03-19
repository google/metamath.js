include "cs3.mm"
include "cs4.mm"
include "c3.mm"
include "cc0.mm"
include "df-s4.mm"
include "s3cli.mm"
include "s3len.mm"
include "s3fv0.mm"
include "0nn0.mm"
include "3pos.mm"
include "cats1fv.mm"

theorem s4fv0
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V


  assert |- ( A e. V -> ( <" A B C D "> ` 0 ) = A )

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
    cc0
    cV
    cD
    cA
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
    s3fv0
    0nn0
    3pos
    cats1fv
end
