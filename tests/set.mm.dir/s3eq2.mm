include "wceq.mm"
include "eqidd.mm"
include "id.mm"
include "s3eqd.mm"

theorem s3eq2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( B = D -> <" A B C "> = <" A D C "> )

  proof
    cB
    cD
    wceq
    #
    cA
    cB
    cC
    cC
    cA
    cD
    @0
    cA
    eqidd
    @0
    id
    @0
    cC
    eqidd
    s3eqd
end
