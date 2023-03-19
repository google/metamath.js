include "cs2.mm"
include "cs3.mm"
include "c2.mm"
include "c1.mm"
include "df-s3.mm"
include "s2cli.mm"
include "s2len.mm"
include "s2fv1.mm"
include "1nn0.mm"
include "1lt2.mm"
include "cats1fv.mm"

theorem s3fv1
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( B e. V -> ( <" A B C "> ` 1 ) = B )

  proof
    cA
    cB
    cs2
    cA
    cB
    cC
    cs3
    c2
    c1
    cV
    cC
    cB
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
    cA
    cB
    cV
    s2fv1
    1nn0
    1lt2
    cats1fv
end
