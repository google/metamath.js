include "wrel.mm"
include "ccnv.mm"
include "wceq.mm"
include "cvv.mm"
include "cres.mm"
include "dfrel2.mm"
include "cnvcnv2.mm"
include "eqeq1i.mm"
include "bitri.mm"

theorem dfrel3
  let cR: class R


  assert |- ( Rel R <-> ( R |` _V ) = R )

  proof
    cR
    wrel
    cR
    ccnv
    ccnv
    #
    cR
    wceq
    cR
    cvv
    cres
    #
    cR
    wceq
    cR
    dfrel2
    @0
    @1
    cR
    cR
    cnvcnv2
    eqeq1i
    bitri
end
