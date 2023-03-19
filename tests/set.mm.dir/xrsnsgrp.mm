include "c1.mm"
include "cxr.mm"
include "wcel.mm"
include "cmnf.mm"
include "cpnf.mm"
include "w3a.mm"
include "cxad.mm"
include "co.mm"
include "wne.mm"
include "cxrs.mm"
include "csgrp.mm"
include "wnel.mm"
include "1re.mm"
include "rexri.mm"
include "mnfxr.mm"
include "pnfxr.mm"
include "3pm3.2i.mm"
include "cc0.mm"
include "wceq.mm"
include "xaddcom.mm"
include "mp2an.mm"
include "cr.mm"
include "renepnf.mm"
include "ax-mp.mm"
include "xaddmnf2.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "mnfaddpnf.mm"
include "0ne1.mm"
include "eqnetri.mm"
include "oveq2i.mm"
include "xaddid1.mm"
include "neeqtrri.mm"
include "xrsbas.mm"
include "xrsadd.mm"
include "isnsgrp.mm"
include "mp2.mm"

theorem xrsnsgrp
  let vx: setvar x
  let vy: setvar y


  assert |- RR*s e/ SGrp

  proof
    c1
    cxr
    wcel
    #
    cmnf
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    w3a
    c1
    cmnf
    cxad
    co
    #
    cpnf
    cxad
    co
    #
    c1
    cmnf
    cpnf
    cxad
    co
    #
    cxad
    co
    #
    wne
    cxrs
    csgrp
    wnel
    @0
    @1
    @2
    c1
    1re
    rexri
    #
    mnfxr
    pnfxr
    3pm3.2i
    @4
    c1
    @6
    @4
    cc0
    c1
    @4
    @5
    cc0
    @3
    cmnf
    cpnf
    cxad
    @3
    cmnf
    c1
    cxad
    co
    #
    cmnf
    @0
    @1
    @3
    @8
    wceq
    @7
    mnfxr
    c1
    cmnf
    xaddcom
    mp2an
    @0
    c1
    cpnf
    wne
    #
    @8
    cmnf
    wceq
    @7
    c1
    cr
    wcel
    @9
    1re
    c1
    renepnf
    ax-mp
    c1
    xaddmnf2
    mp2an
    eqtri
    oveq1i
    mnfaddpnf
    eqtri
    0ne1
    eqnetri
    @6
    c1
    cc0
    cxad
    co
    #
    c1
    @5
    cc0
    c1
    cxad
    mnfaddpnf
    oveq2i
    @0
    @10
    c1
    wceq
    @7
    c1
    xaddid1
    ax-mp
    eqtri
    neeqtrri
    cxr
    cxrs
    c1
    cmnf
    cxad
    cpnf
    xrsbas
    xrsadd
    isnsgrp
    mp2
end
