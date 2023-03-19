include "crtcl.mm"
include "ctcl.mm"
include "ccom.mm"
include "crcl.mm"
include "corcltrcl.mm"
include "eqcomi.mm"
include "coeq1i.mm"
include "coass.mm"
include "cotrcltrcl.mm"
include "coeq2i.mm"
include "eqtri.mm"

theorem cortrcltrcl



  assert |- ( t* o. t+ ) = t*

  proof
    crtcl
    ctcl
    ccom
    crcl
    ctcl
    ccom
    #
    ctcl
    ccom
    #
    crtcl
    crtcl
    @0
    ctcl
    @0
    crtcl
    corcltrcl
    eqcomi
    coeq1i
    @1
    crcl
    ctcl
    ctcl
    ccom
    #
    ccom
    #
    crtcl
    crcl
    ctcl
    ctcl
    coass
    @3
    @0
    crtcl
    @2
    ctcl
    crcl
    cotrcltrcl
    coeq2i
    corcltrcl
    eqtri
    eqtri
    eqtri
end
