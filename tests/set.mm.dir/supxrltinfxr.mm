include "cmnf.mm"
include "cpnf.mm"
include "c0.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cinf.mm"
include "mnfltpnf.mm"
include "xrsup0.mm"
include "xrinf0.mm"
include "3brtr4i.mm"

theorem supxrltinfxr



  assert |- sup ( (/) , RR* , < ) < inf ( (/) , RR* , < )

  proof
    cmnf
    cpnf
    c0
    cxr
    clt
    csup
    c0
    cxr
    clt
    cinf
    clt
    mnfltpnf
    xrsup0
    xrinf0
    3brtr4i
end
