include "cxr.mm"
include "wcel.mm"
include "cmnf.mm"
include "wne.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "simpr.mm"
include "neneqd.mm"
include "wb.mm"
include "ngtmnft.mm"
include "adantr.mm"
include "mtbid.mm"
include "notnotb.mm"
include "sylibr.mm"

theorem nemnftgtmnft
  let cA: class A


  assert |- ( ( A e. RR* /\ A =/= -oo ) -> -oo < A )

  proof
    cA
    cxr
    wcel
    #
    cA
    cmnf
    wne
    #
    wa
    #
    cmnf
    cA
    clt
    wbr
    #
    wn
    #
    wn
    @3
    @2
    cA
    cmnf
    wceq
    #
    @4
    @2
    cA
    cmnf
    @0
    @1
    simpr
    neneqd
    @0
    @5
    @4
    wb
    @1
    cA
    ngtmnft
    adantr
    mtbid
    @3
    notnotb
    sylibr
end
