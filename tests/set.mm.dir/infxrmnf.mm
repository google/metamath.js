include "cxr.mm"
include "wss.mm"
include "cmnf.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "cinf.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "infxrlb.mm"
include "wb.mm"
include "infxrcl.mm"
include "adantr.mm"
include "xlemnf.mm"
include "syl.mm"
include "mpbid.mm"

theorem infxrmnf
  let cA: class A


  assert |- ( ( A C_ RR* /\ -oo e. A ) -> inf ( A , RR* , < ) = -oo )

  proof
    cA
    cxr
    wss
    #
    cmnf
    cA
    wcel
    #
    wa
    #
    cA
    cxr
    clt
    cinf
    #
    cmnf
    cle
    wbr
    #
    @3
    cmnf
    wceq
    #
    cA
    cmnf
    infxrlb
    @2
    @3
    cxr
    wcel
    #
    @4
    @5
    wb
    @0
    @6
    @1
    cA
    infxrcl
    adantr
    @3
    xlemnf
    syl
    mpbid
end
