include "cres.mm"
include "cin.mm"
include "inres.mm"
include "ineqcomi.mm"
include "incom.mm"
include "reseq1i.mm"
include "eqtr4i.mm"

theorem inres2
  let cA: class A
  let cR: class R
  let cS: class S


  assert |- ( ( R |` A ) i^i S ) = ( ( R i^i S ) |` A )

  proof
    cR
    cA
    cres
    #
    cS
    cin
    cS
    cR
    cin
    #
    cA
    cres
    #
    cR
    cS
    cin
    #
    cA
    cres
    cS
    @0
    @2
    cS
    cR
    cA
    inres
    ineqcomi
    @3
    @1
    cA
    cR
    cS
    incom
    reseq1i
    eqtr4i
end
