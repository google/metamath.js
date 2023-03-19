include "cxr.mm"
include "wss.mm"
include "cmnf.mm"
include "wcel.mm"
include "clt.mm"
include "cinf.mm"
include "wceq.mm"
include "ssid.mm"
include "mnfxr.mm"
include "infxrmnf.mm"
include "mp2an.mm"

theorem xrinfm



  assert |- inf ( RR* , RR* , < ) = -oo

  proof
    cxr
    cxr
    wss
    cmnf
    cxr
    wcel
    cxr
    cxr
    clt
    cinf
    cmnf
    wceq
    cxr
    ssid
    mnfxr
    cxr
    infxrmnf
    mp2an
end
