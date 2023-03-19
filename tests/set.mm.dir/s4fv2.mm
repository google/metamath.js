include "cs3.mm"
include "cs4.mm"
include "c3.mm"
include "c2.mm"
include "df-s4.mm"
include "s3cli.mm"
include "s3len.mm"
include "s3fv2.mm"
include "2nn0.mm"
include "2lt3.mm"
include "cats1fv.mm"

theorem s4fv2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V


  assert |- ( C e. V -> ( <" A B C D "> ` 2 ) = C )

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
    c2
    cV
    cD
    cC
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
    s3fv2
    2nn0
    2lt3
    cats1fv
end
