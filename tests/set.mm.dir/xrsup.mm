include "cxr.mm"
include "wss.mm"
include "cpnf.mm"
include "wcel.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "ssid.mm"
include "pnfxr.mm"
include "supxrpnf.mm"
include "mp2an.mm"

theorem xrsup



  assert |- sup ( RR* , RR* , < ) = +oo

  proof
    cxr
    cxr
    wss
    cpnf
    cxr
    wcel
    cxr
    cxr
    clt
    csup
    cpnf
    wceq
    cxr
    ssid
    pnfxr
    cxr
    supxrpnf
    mp2an
end
