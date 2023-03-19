include "cs3.mm"
include "cs4.mm"
include "c3.mm"
include "c4.mm"
include "df-s4.mm"
include "s3cli.mm"
include "s3len.mm"
include "3p1e4.mm"
include "cats1len.mm"

theorem s4len
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( # ` <" A B C D "> ) = 4

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
    c4
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
    3p1e4
    cats1len
end
