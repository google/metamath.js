include "cpr.mm"
include "cdif.mm"
include "csn.mm"
include "cun.mm"
include "df-pr.mm"
include "difeq2i.mm"
include "difun1.mm"
include "eqtri.mm"

theorem difpr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A \ { B , C } ) = ( ( A \ { B } ) \ { C } )

  proof
    cA
    cB
    cC
    cpr
    #
    cdif
    cA
    cB
    csn
    #
    cC
    csn
    #
    cun
    #
    cdif
    cA
    @1
    cdif
    @2
    cdif
    @0
    @3
    cA
    cB
    cC
    df-pr
    difeq2i
    cA
    @1
    @2
    difun1
    eqtri
end
