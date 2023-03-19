include "cs2.mm"
include "cs3.mm"
include "c2.mm"
include "df-s3.mm"
include "s2cli.mm"
include "s2len.mm"
include "cats1fvn.mm"

theorem s3fv2
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( C e. V -> ( <" A B C "> ` 2 ) = C )

  proof
    cA
    cB
    cs2
    cA
    cB
    cC
    cs3
    c2
    cV
    cC
    cA
    cB
    cC
    df-s3
    cA
    cB
    s2cli
    cA
    cB
    s2len
    cats1fvn
end
