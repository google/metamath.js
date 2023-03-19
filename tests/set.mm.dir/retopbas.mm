include "cioo.mm"
include "cxr.mm"
include "cxp.mm"
include "cima.mm"
include "crn.mm"
include "ctb.mm"
include "cdm.mm"
include "cr.mm"
include "cpw.mm"
include "ioof.mm"
include "fdmi.mm"
include "imaeq2i.mm"
include "imadmrn.mm"
include "eqtr3i.mm"
include "ssid.mm"
include "qtopbaslem.mm"
include "eqeltrri.mm"

theorem retopbas



  assert |- ran (,) e. TopBases

  proof
    cioo
    cxr
    cxr
    cxp
    #
    cima
    #
    cioo
    crn
    #
    ctb
    cioo
    cioo
    cdm
    #
    cima
    @1
    @2
    @3
    @0
    cioo
    @0
    cr
    cpw
    cioo
    ioof
    fdmi
    imaeq2i
    cioo
    imadmrn
    eqtr3i
    cxr
    cxr
    ssid
    qtopbaslem
    eqeltrri
end
