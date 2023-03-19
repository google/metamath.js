include "cr.mm"
include "covol.mm"
include "cfv.mm"
include "cpnf.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cxr.mm"
include "wcel.mm"
include "wss.mm"
include "ssid.mm"
include "ovolcl.mm"
include "ax-mp.mm"
include "pnfge.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "0re.mm"
include "ovolicopnf.mm"
include "rge0ssre.mm"
include "ovolss.mm"
include "mp2an.mm"
include "eqbrtrri.mm"
include "wa.mm"
include "wb.mm"
include "pnfxr.mm"
include "xrletri3.mm"
include "mpbir2an.mm"

theorem ovolre



  assert |- ( vol* ` RR ) = +oo

  proof
    cr
    covol
    cfv
    #
    cpnf
    wceq
    #
    @0
    cpnf
    cle
    wbr
    #
    cpnf
    @0
    cle
    wbr
    #
    @0
    cxr
    wcel
    #
    @2
    cr
    cr
    wss
    #
    @4
    cr
    ssid
    #
    cr
    ovolcl
    ax-mp
    #
    @0
    pnfge
    ax-mp
    cc0
    cpnf
    cico
    co
    #
    covol
    cfv
    #
    cpnf
    @0
    cle
    cc0
    cr
    wcel
    @9
    cpnf
    wceq
    0re
    cc0
    ovolicopnf
    ax-mp
    @8
    cr
    wss
    @5
    @9
    @0
    cle
    wbr
    rge0ssre
    @6
    @8
    cr
    ovolss
    mp2an
    eqbrtrri
    @4
    cpnf
    cxr
    wcel
    @1
    @2
    @3
    wa
    wb
    @7
    pnfxr
    @0
    cpnf
    xrletri3
    mp2an
    mpbir2an
end
