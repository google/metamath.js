include "wrel.mm"
include "ccnv.mm"
include "wceq.mm"
include "cdm.mm"
include "cres.mm"
include "dfrel2.mm"
include "resdm2.mm"
include "eqeq1i.mm"
include "bitr4i.mm"

theorem dfrel5
  let cR: class R


  assert |- ( Rel R <-> ( R |` dom R ) = R )

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
    cR
    cdm
    cres
    #
    cR
    wceq
    cR
    dfrel2
    @1
    @0
    cR
    cR
    resdm2
    eqeq1i
    bitr4i
end
