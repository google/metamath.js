include "cs2.mm"
include "cs3.mm"
include "c2.mm"
include "cc0.mm"
include "df-s3.mm"
include "s2cli.mm"
include "s2len.mm"
include "s2fv0.mm"
include "0nn0.mm"
include "2pos.mm"
include "cats1fv.mm"

theorem s3fv0
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( A e. V -> ( <" A B C "> ` 0 ) = A )

  proof
    cA
    cB
    cs2
    cA
    cB
    cC
    cs3
    c2
    cc0
    cV
    cC
    cA
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
    s2fv0
    0nn0
    2pos
    cats1fv
end
