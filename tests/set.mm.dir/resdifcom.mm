include "cdif.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "cres.mm"
include "indif1.mm"
include "df-res.mm"
include "difeq1i.mm"
include "3eqtr4ri.mm"

theorem resdifcom
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A |` B ) \ C ) = ( ( A \ C ) |` B )

  proof
    cA
    cC
    cdif
    #
    cB
    cvv
    cxp
    #
    cin
    cA
    @1
    cin
    #
    cC
    cdif
    @0
    cB
    cres
    cA
    cB
    cres
    #
    cC
    cdif
    cA
    @1
    cC
    indif1
    @0
    cB
    df-res
    @3
    @2
    cC
    cA
    cB
    df-res
    difeq1i
    3eqtr4ri
end
