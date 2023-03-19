include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wne.mm"
include "clt.mm"
include "wo.mm"
include "wb.mm"
include "0re.mm"
include "lttri2.mm"
include "mpan2.mm"
include "adantr.mm"
include "wn.mm"
include "lenlt.mm"
include "mpan.mm"
include "biimpa.mm"
include "biorf.mm"
include "syl.mm"
include "bitr4d.mm"

theorem ne0gt0
  let cA: class A


  assert |- ( ( A e. RR /\ 0 <_ A ) -> ( A =/= 0 <-> 0 < A ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cA
    cc0
    wne
    #
    cA
    cc0
    clt
    wbr
    #
    cc0
    cA
    clt
    wbr
    #
    wo
    #
    @5
    @0
    @3
    @6
    wb
    #
    @1
    @0
    cc0
    cr
    wcel
    #
    @7
    0re
    cA
    cc0
    lttri2
    mpan2
    adantr
    @2
    @4
    wn
    #
    @5
    @6
    wb
    @0
    @1
    @9
    @8
    @0
    @1
    @9
    wb
    0re
    cc0
    cA
    lenlt
    mpan
    biimpa
    @4
    @5
    biorf
    syl
    bitr4d
end
