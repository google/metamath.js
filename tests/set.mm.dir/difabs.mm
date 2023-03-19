include "cun.mm"
include "cdif.mm"
include "difun1.mm"
include "unidm.mm"
include "difeq2i.mm"
include "eqtr3i.mm"

theorem difabs
  let cA: class A
  let cB: class B


  assert |- ( ( A \ B ) \ B ) = ( A \ B )

  proof
    cA
    cB
    cB
    cun
    #
    cdif
    cA
    cB
    cdif
    #
    cB
    cdif
    @1
    cA
    cB
    cB
    difun1
    @0
    cB
    cA
    cB
    unidm
    difeq2i
    eqtr3i
end
