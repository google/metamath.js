include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cpnf.mm"
include "cxmu.mm"
include "co.mm"
include "wceq.mm"
include "wo.mm"
include "cmnf.mm"
include "cmul.mm"
include "cif.mm"
include "pnfxr.mm"
include "xmulval.mm"
include "mpan2.mm"
include "adantr.mm"
include "wne.mm"
include "wn.mm"
include "0xr.mm"
include "xrltne.mm"
include "mp3an1.mm"
include "cr.mm"
include "0re.mm"
include "renepnf.mm"
include "ax-mp.mm"
include "necomi.mm"
include "jctir.mm"
include "neanior.mm"
include "sylib.mm"
include "iffalsed.mm"
include "simpr.mm"
include "eqid.mm"
include "orcd.mm"
include "olcd.mm"
include "iftrued.mm"
include "3eqtrd.mm"

theorem xmulpnf1
  let cA: class A


  assert |- ( ( A e. RR* /\ 0 < A ) -> ( A *e +oo ) = +oo )

  proof
    cA
    cxr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    cA
    cpnf
    cxmu
    co
    #
    cA
    cc0
    wceq
    cpnf
    cc0
    wceq
    wo
    #
    cc0
    cc0
    cpnf
    clt
    wbr
    #
    cA
    cpnf
    wceq
    #
    wa
    cpnf
    cc0
    clt
    wbr
    #
    cA
    cmnf
    wceq
    #
    wa
    wo
    #
    @1
    cpnf
    cpnf
    wceq
    #
    wa
    #
    cA
    cc0
    clt
    wbr
    #
    cpnf
    cmnf
    wceq
    #
    wa
    #
    wo
    #
    wo
    #
    cpnf
    @5
    @8
    wa
    @7
    @6
    wa
    wo
    @1
    @13
    wa
    @12
    @10
    wa
    wo
    wo
    cmnf
    cA
    cpnf
    cmul
    co
    cif
    #
    cif
    #
    cif
    #
    @18
    cpnf
    @0
    @3
    @19
    wceq
    #
    @1
    @0
    cpnf
    cxr
    wcel
    @20
    pnfxr
    cA
    cpnf
    xmulval
    mpan2
    adantr
    @2
    @4
    cc0
    @18
    @2
    cA
    cc0
    wne
    #
    cpnf
    cc0
    wne
    #
    wa
    @4
    wn
    @2
    @21
    @22
    cc0
    cxr
    wcel
    @0
    @1
    @21
    0xr
    cc0
    cA
    xrltne
    mp3an1
    cc0
    cpnf
    cc0
    cr
    wcel
    cc0
    cpnf
    wne
    0re
    cc0
    renepnf
    ax-mp
    necomi
    jctir
    cA
    cc0
    cpnf
    cc0
    neanior
    sylib
    iffalsed
    @2
    @16
    cpnf
    @17
    @2
    @15
    @9
    @2
    @11
    @14
    @2
    @1
    @10
    @0
    @1
    simpr
    cpnf
    eqid
    jctir
    orcd
    olcd
    iftrued
    3eqtrd
end
