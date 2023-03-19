include "cpnf.mm"
include "cmnf.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "caddc.mm"
include "cxr.mm"
include "wcel.mm"
include "pnfxr.mm"
include "mnfxr.mm"
include "xaddval.mm"
include "mp2an.mm"
include "eqid.mm"
include "iftruei.mm"
include "3eqtri.mm"

theorem pnfaddmnf



  assert |- ( +oo +e -oo ) = 0

  proof
    cpnf
    cmnf
    cxad
    co
    #
    cpnf
    cpnf
    wceq
    #
    cmnf
    cmnf
    wceq
    #
    cc0
    cpnf
    cif
    #
    cpnf
    cmnf
    wceq
    cmnf
    cpnf
    wceq
    #
    cc0
    cmnf
    cif
    @4
    cpnf
    @2
    cmnf
    cpnf
    cmnf
    caddc
    co
    cif
    cif
    cif
    #
    cif
    #
    @3
    cc0
    cpnf
    cxr
    wcel
    cmnf
    cxr
    wcel
    @0
    @6
    wceq
    pnfxr
    mnfxr
    cpnf
    cmnf
    xaddval
    mp2an
    @1
    @3
    @5
    cpnf
    eqid
    iftruei
    @2
    cc0
    cpnf
    cmnf
    eqid
    iftruei
    3eqtri
end
