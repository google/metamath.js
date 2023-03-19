include "cid.mm"
include "wrefrel.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "wrel.mm"
include "ssid.mm"
include "reli.mm"
include "df-refrel.mm"
include "mpbir2an.mm"

theorem refrelid



  assert |- RefRel _I

  proof
    cid
    wrefrel
    cid
    cid
    cdm
    cid
    crn
    cxp
    cin
    #
    @0
    wss
    cid
    wrel
    @0
    ssid
    reli
    cid
    df-refrel
    mpbir2an
end
