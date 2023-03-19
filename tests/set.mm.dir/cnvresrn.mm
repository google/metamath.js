include "ccnv.mm"
include "crn.mm"
include "cres.mm"
include "cdm.mm"
include "df-rn.mm"
include "reseq2i.mm"
include "wrel.mm"
include "wceq.mm"
include "relcnv.mm"
include "dfrel5.mm"
include "mpbi.mm"
include "eqtri.mm"

theorem cnvresrn
  let cR: class R


  assert |- ( `' R |` ran R ) = `' R

  proof
    cR
    ccnv
    #
    cR
    crn
    #
    cres
    @0
    @0
    cdm
    #
    cres
    #
    @0
    @1
    @2
    @0
    cR
    df-rn
    reseq2i
    @0
    wrel
    @3
    @0
    wceq
    cR
    relcnv
    @0
    dfrel5
    mpbi
    eqtri
end
