include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmnf.mm"
include "clt.mm"
include "wne.mm"
include "ge0gtmnf.mm"
include "wceq.mm"
include "wn.mm"
include "wb.mm"
include "ngtmnft.mm"
include "adantr.mm"
include "necon2abid.mm"
include "mpbid.mm"

theorem ge0nemnf
  let cA: class A


  assert |- ( ( A e. RR* /\ 0 <_ A ) -> A =/= -oo )

  proof
    cA
    cxr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cmnf
    cA
    clt
    wbr
    #
    cA
    cmnf
    wne
    cA
    ge0gtmnf
    @2
    @3
    cA
    cmnf
    @0
    cA
    cmnf
    wceq
    @3
    wn
    wb
    @1
    cA
    ngtmnft
    adantr
    necon2abid
    mpbid
end
