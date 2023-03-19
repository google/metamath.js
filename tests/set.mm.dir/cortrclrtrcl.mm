include "crtcl.mm"
include "ccom.mm"
include "ctcl.mm"
include "crcl.mm"
include "cotrclrcl.mm"
include "eqcomi.mm"
include "coeq1i.mm"
include "coass.mm"
include "corclrtrcl.mm"
include "coeq2i.mm"
include "cotrclrtrcl.mm"
include "eqtri.mm"

theorem cortrclrtrcl



  assert |- ( t* o. t* ) = t*

  proof
    crtcl
    crtcl
    ccom
    ctcl
    crcl
    ccom
    #
    crtcl
    ccom
    #
    crtcl
    crtcl
    @0
    crtcl
    @0
    crtcl
    cotrclrcl
    eqcomi
    coeq1i
    @1
    ctcl
    crcl
    crtcl
    ccom
    #
    ccom
    #
    crtcl
    ctcl
    crcl
    crtcl
    coass
    @3
    ctcl
    crtcl
    ccom
    crtcl
    @2
    crtcl
    ctcl
    corclrtrcl
    coeq2i
    cotrclrtrcl
    eqtri
    eqtri
    eqtri
end
