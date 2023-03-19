include "cs2.mm"
include "cs3.mm"
include "c2.mm"
include "c3.mm"
include "df-s3.mm"
include "s2cli.mm"
include "s2len.mm"
include "2p1e3.mm"
include "cats1len.mm"

theorem s3len
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( # ` <" A B C "> ) = 3

  proof
    cA
    cB
    cs2
    cA
    cB
    cC
    cs3
    c2
    c3
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
    2p1e3
    cats1len
end
