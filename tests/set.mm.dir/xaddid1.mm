include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "w3o.mm"
include "cc0.mm"
include "cxad.mm"
include "co.mm"
include "elxr.mm"
include "caddc.mm"
include "0re.mm"
include "rexadd.mm"
include "mpan2.mm"
include "recn.mm"
include "addid1d.mm"
include "eqtrd.mm"
include "wne.mm"
include "0xr.mm"
include "renemnf.mm"
include "ax-mp.mm"
include "xaddpnf2.mm"
include "mp2an.mm"
include "oveq1.mm"
include "id.mm"
include "3eqtr4a.mm"
include "renepnf.mm"
include "xaddmnf2.mm"
include "3jaoi.mm"
include "sylbi.mm"

theorem xaddid1
  let cA: class A


  assert |- ( A e. RR* -> ( A +e 0 ) = A )

  proof
    cA
    cxr
    wcel
    cA
    cr
    wcel
    #
    cA
    cpnf
    wceq
    #
    cA
    cmnf
    wceq
    #
    w3o
    cA
    cc0
    cxad
    co
    #
    cA
    wceq
    #
    cA
    elxr
    @0
    @4
    @1
    @2
    @0
    @3
    cA
    cc0
    caddc
    co
    #
    cA
    @0
    cc0
    cr
    wcel
    #
    @3
    @5
    wceq
    0re
    cA
    cc0
    rexadd
    mpan2
    @0
    cA
    cA
    recn
    addid1d
    eqtrd
    @1
    cpnf
    cc0
    cxad
    co
    #
    cpnf
    @3
    cA
    cc0
    cxr
    wcel
    #
    cc0
    cmnf
    wne
    #
    @7
    cpnf
    wceq
    0xr
    @6
    @9
    0re
    cc0
    renemnf
    ax-mp
    cc0
    xaddpnf2
    mp2an
    cA
    cpnf
    cc0
    cxad
    oveq1
    @1
    id
    3eqtr4a
    @2
    cmnf
    cc0
    cxad
    co
    #
    cmnf
    @3
    cA
    @8
    cc0
    cpnf
    wne
    #
    @10
    cmnf
    wceq
    0xr
    @6
    @11
    0re
    cc0
    renepnf
    ax-mp
    cc0
    xaddmnf2
    mp2an
    cA
    cmnf
    cc0
    cxad
    oveq1
    @2
    id
    3eqtr4a
    3jaoi
    sylbi
end
