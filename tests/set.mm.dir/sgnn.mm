include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "csgn.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "cif.mm"
include "sgnval.mm"
include "adantr.mm"
include "wne.mm"
include "wn.mm"
include "0xr.mm"
include "xrltne.mm"
include "mp3an2.mm"
include "nesym.mm"
include "sylib.mm"
include "iffalsed.mm"
include "iftrue.mm"
include "adantl.mm"
include "3eqtrd.mm"

theorem sgnn
  let cA: class A


  assert |- ( ( A e. RR* /\ A < 0 ) -> ( sgn ` A ) = -u 1 )

  proof
    cA
    cxr
    wcel
    #
    cA
    cc0
    clt
    wbr
    #
    wa
    #
    cA
    csgn
    cfv
    #
    cA
    cc0
    wceq
    #
    cc0
    @1
    c1
    cneg
    #
    c1
    cif
    #
    cif
    #
    @6
    @5
    @0
    @3
    @7
    wceq
    @1
    cA
    sgnval
    adantr
    @2
    @4
    cc0
    @6
    @2
    cc0
    cA
    wne
    #
    @4
    wn
    @0
    cc0
    cxr
    wcel
    @1
    @8
    0xr
    cA
    cc0
    xrltne
    mp3an2
    cc0
    cA
    nesym
    sylib
    iffalsed
    @1
    @6
    @5
    wceq
    @0
    @1
    @5
    c1
    iftrue
    adantl
    3eqtrd
end
