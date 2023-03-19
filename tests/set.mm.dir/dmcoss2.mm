include "ccoss.mm"
include "cdm.mm"
include "ccnv.mm"
include "crn.mm"
include "dmcoss3.mm"
include "df-rn.mm"
include "eqtr4i.mm"

theorem dmcoss2
  let cR: class R


  assert |- dom ,~ R = ran R

  proof
    cR
    ccoss
    cdm
    cR
    ccnv
    cdm
    cR
    crn
    cR
    dmcoss3
    cR
    df-rn
    eqtr4i
end
