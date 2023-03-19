include "crtcl.mm"
include "crcl.mm"
include "ccom.mm"
include "ctcl.mm"
include "cotrclrcl.mm"
include "eqcomi.mm"
include "coeq1i.mm"
include "coass.mm"
include "corclrcl.mm"
include "coeq2i.mm"
include "eqtri.mm"

theorem cortrclrcl



  assert |- ( t* o. r* ) = t*

  proof
    crtcl
    crcl
    ccom
    ctcl
    crcl
    ccom
    #
    crcl
    ccom
    #
    crtcl
    crtcl
    @0
    crcl
    @0
    crtcl
    cotrclrcl
    eqcomi
    coeq1i
    @1
    ctcl
    crcl
    crcl
    ccom
    #
    ccom
    #
    crtcl
    ctcl
    crcl
    crcl
    coass
    @3
    @0
    crtcl
    @2
    crcl
    ctcl
    corclrcl
    coeq2i
    cotrclrcl
    eqtri
    eqtri
    eqtri
end
