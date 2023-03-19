include "wrel.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "dfrel5.mm"
include "dfres3.mm"
include "eqeq1i.mm"
include "bitri.mm"

theorem dfrel6
  let cR: class R


  assert |- ( Rel R <-> ( R i^i ( dom R X. ran R ) ) = R )

  proof
    cR
    wrel
    cR
    cR
    cdm
    #
    cres
    #
    cR
    wceq
    cR
    @0
    cR
    crn
    cxp
    cin
    #
    cR
    wceq
    cR
    dfrel5
    @1
    @2
    cR
    cR
    @0
    dfres3
    eqeq1i
    bitri
end
