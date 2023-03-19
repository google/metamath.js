include "ccoss.mm"
include "wrefrel.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "wrel.mm"
include "wa.mm"
include "refrelcoss2.mm"
include "dfrefrel2.mm"
include "mpbir.mm"

theorem refrelcoss
  let cR: class R


  assert |- RefRel ,~ R

  proof
    cR
    ccoss
    #
    wrefrel
    cid
    @0
    cdm
    @0
    crn
    cxp
    cin
    @0
    wss
    @0
    wrel
    wa
    cR
    refrelcoss2
    @0
    dfrefrel2
    mpbir
end
