include "cmnf.mm"
include "cpnf.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "caddc.mm"
include "cxr.mm"
include "wcel.mm"
include "mnfxr.mm"
include "pnfxr.mm"
include "xaddval.mm"
include "mp2an.mm"
include "wne.mm"
include "mnfnepnf.mm"
include "ifnefalse.mm"
include "ax-mp.mm"
include "eqid.mm"
include "iftruei.mm"
include "eqtri.mm"

theorem mnfaddpnf



  assert |- ( -oo +e +oo ) = 0

  proof
    cmnf
    cpnf
    cxad
    co
    #
    cmnf
    cpnf
    wceq
    cpnf
    cmnf
    wceq
    #
    cc0
    cpnf
    cif
    #
    cmnf
    cmnf
    wceq
    #
    cpnf
    cpnf
    wceq
    #
    cc0
    cmnf
    cif
    #
    @4
    cpnf
    @1
    cmnf
    cmnf
    cpnf
    caddc
    co
    cif
    cif
    #
    cif
    #
    cif
    #
    cc0
    cmnf
    cxr
    wcel
    cpnf
    cxr
    wcel
    @0
    @8
    wceq
    mnfxr
    pnfxr
    cmnf
    cpnf
    xaddval
    mp2an
    @8
    @7
    cc0
    cmnf
    cpnf
    wne
    @8
    @7
    wceq
    mnfnepnf
    cmnf
    cpnf
    @2
    @7
    ifnefalse
    ax-mp
    @7
    @5
    cc0
    @3
    @5
    @6
    cmnf
    eqid
    iftruei
    @4
    cc0
    cmnf
    cpnf
    eqid
    iftruei
    eqtri
    eqtri
    eqtri
end
