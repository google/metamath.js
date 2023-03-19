include "crcl.mm"
include "crtcl.mm"
include "ccom.mm"
include "ctcl.mm"
include "corcltrcl.mm"
include "eqcomi.mm"
include "coeq2i.mm"
include "coass.mm"
include "corclrcl.mm"
include "coeq1i.mm"
include "eqtri.mm"

theorem corclrtrcl



  assert |- ( r* o. t* ) = t*

  proof
    crcl
    crtcl
    ccom
    crcl
    crcl
    ctcl
    ccom
    #
    ccom
    #
    crtcl
    crtcl
    @0
    crcl
    @0
    crtcl
    corcltrcl
    eqcomi
    coeq2i
    @1
    crcl
    crcl
    ccom
    #
    ctcl
    ccom
    #
    crtcl
    @3
    @1
    crcl
    crcl
    ctcl
    coass
    eqcomi
    @3
    @0
    crtcl
    @2
    crcl
    ctcl
    corclrcl
    coeq1i
    corcltrcl
    eqtri
    eqtri
    eqtri
end
