include "ctcl.mm"
include "crtcl.mm"
include "ccom.mm"
include "crcl.mm"
include "cotrclrcl.mm"
include "eqcomi.mm"
include "coeq2i.mm"
include "coass.mm"
include "cotrcltrcl.mm"
include "coeq1i.mm"
include "eqtri.mm"

theorem cotrclrtrcl



  assert |- ( t+ o. t* ) = t*

  proof
    ctcl
    crtcl
    ccom
    ctcl
    ctcl
    crcl
    ccom
    #
    ccom
    #
    crtcl
    crtcl
    @0
    ctcl
    @0
    crtcl
    cotrclrcl
    eqcomi
    coeq2i
    @1
    ctcl
    ctcl
    ccom
    #
    crcl
    ccom
    #
    crtcl
    @3
    @1
    ctcl
    ctcl
    crcl
    coass
    eqcomi
    @3
    @0
    crtcl
    @2
    ctcl
    crcl
    cotrcltrcl
    coeq1i
    cotrclrcl
    eqtri
    eqtri
    eqtri
end
