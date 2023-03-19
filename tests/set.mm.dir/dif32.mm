include "cun.mm"
include "cdif.mm"
include "uncom.mm"
include "difeq2i.mm"
include "difun1.mm"
include "3eqtr3i.mm"

theorem dif32
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A \ B ) \ C ) = ( ( A \ C ) \ B )

  proof
    cA
    cB
    cC
    cun
    #
    cdif
    cA
    cC
    cB
    cun
    #
    cdif
    cA
    cB
    cdif
    cC
    cdif
    cA
    cC
    cdif
    cB
    cdif
    @0
    @1
    cA
    cB
    cC
    uncom
    difeq2i
    cA
    cB
    cC
    difun1
    cA
    cC
    cB
    difun1
    3eqtr3i
end
