include "ccoss.mm"
include "cdm.mm"
include "ccnv.mm"
include "ccom.mm"
include "dfcoss3.mm"
include "dmeqi.mm"
include "crn.mm"
include "wss.mm"
include "wceq.mm"
include "rncnv.mm"
include "eqimssi.mm"
include "dmcosseq.mm"
include "ax-mp.mm"
include "eqtri.mm"

theorem dmcoss3
  let cR: class R


  assert |- dom ,~ R = dom `' R

  proof
    cR
    ccoss
    #
    cdm
    cR
    cR
    ccnv
    #
    ccom
    #
    cdm
    #
    @1
    cdm
    #
    @0
    @2
    cR
    dfcoss3
    dmeqi
    @1
    crn
    #
    cR
    cdm
    #
    wss
    @3
    @4
    wceq
    @5
    @6
    cR
    rncnv
    eqimssi
    cR
    @1
    dmcosseq
    ax-mp
    eqtri
end
