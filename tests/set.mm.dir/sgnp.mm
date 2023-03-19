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
include "0xr.mm"
include "xrltne.mm"
include "mp3an1.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "wn.mm"
include "wi.mm"
include "xrltnsym.mm"
include "mpan.mm"
include "imp.mm"
include "3eqtrd.mm"

theorem sgnp
  let cA: class A


  assert |- ( ( A e. RR* /\ 0 < A ) -> ( sgn ` A ) = 1 )

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
    csgn
    cfv
    #
    cA
    cc0
    wceq
    #
    cc0
    cA
    cc0
    clt
    wbr
    #
    c1
    cneg
    #
    c1
    cif
    #
    cif
    #
    @7
    c1
    @0
    @3
    @8
    wceq
    @1
    cA
    sgnval
    adantr
    @2
    @4
    cc0
    @7
    @2
    cA
    cc0
    cc0
    cxr
    wcel
    #
    @0
    @1
    cA
    cc0
    wne
    0xr
    cc0
    cA
    xrltne
    mp3an1
    neneqd
    iffalsed
    @2
    @5
    @6
    c1
    @0
    @1
    @5
    wn
    #
    @9
    @0
    @1
    @10
    wi
    0xr
    cc0
    cA
    xrltnsym
    mpan
    imp
    iffalsed
    3eqtrd
end
