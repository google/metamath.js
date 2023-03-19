include "wrel.mm"
include "cres.mm"
include "cdm.mm"
include "cin.mm"
include "resdm.mm"
include "ineq2d.mm"
include "resindi.mm"
include "incom.mm"
include "inres.mm"
include "inidm.mm"
include "reseq1i.mm"
include "3eqtrri.mm"
include "3eqtr4g.mm"

theorem resindm
  let cA: class A
  let cB: class B


  assert |- ( Rel A -> ( A |` ( B i^i dom A ) ) = ( A |` B ) )

  proof
    cA
    wrel
    #
    cA
    cB
    cres
    #
    cA
    cA
    cdm
    #
    cres
    #
    cin
    @1
    cA
    cin
    #
    cA
    cB
    @2
    cin
    cres
    @1
    @0
    @3
    cA
    @1
    cA
    resdm
    ineq2d
    cA
    cB
    @2
    resindi
    @4
    cA
    @1
    cin
    cA
    cA
    cin
    #
    cB
    cres
    @1
    @1
    cA
    incom
    cA
    cA
    cB
    inres
    @5
    cA
    cB
    cA
    inidm
    reseq1i
    3eqtrri
    3eqtr4g
end
