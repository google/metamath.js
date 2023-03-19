include "wss.mm"
include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "ssid.mm"
include "pjss2coi.mm"
include "mpbi.mm"

theorem pjidmcoi
  let cH: class H
  let vx: setvar x
  assume pjidmco.1: |- H e. CH


  assert |- ( ( projh ` H ) o. ( projh ` H ) ) = ( projh ` H )

  proof
    cH
    cH
    wss
    cH
    cpjh
    cfv
    #
    @0
    ccom
    @0
    wceq
    cH
    ssid
    cH
    cH
    pjidmco.1
    pjidmco.1
    pjss2coi
    mpbi
end
