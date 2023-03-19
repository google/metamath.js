include "wrel.mm"
include "cuni.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "ccnv.mm"
include "relfld.mm"
include "unidmrn.mm"
include "syl6eqr.mm"

theorem relcnvfld
  let cR: class R


  assert |- ( Rel R -> U. U. R = U. U. `' R )

  proof
    cR
    wrel
    cR
    cuni
    cuni
    cR
    cdm
    cR
    crn
    cun
    cR
    ccnv
    cuni
    cuni
    cR
    relfld
    cR
    unidmrn
    syl6eqr
end
