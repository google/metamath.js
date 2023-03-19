include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "wo.mm"
include "ax-icn.mm"
include "mul01i.mm"
include "oveq2i.mm"
include "00id.mm"
include "eqtri.mm"
include "eqeq2i.mm"
include "wb.mm"
include "0re.mm"
include "cru.mm"
include "mpanr12.mm"
include "syl5bbr.mm"
include "necon3abid.mm"
include "neorian.mm"
include "syl6rbbr.mm"

theorem crne0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( A =/= 0 \/ B =/= 0 ) <-> ( A + ( _i x. B ) ) =/= 0 ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    wa
    #
    cA
    ci
    cB
    cmul
    co
    caddc
    co
    #
    cc0
    wne
    cA
    cc0
    wceq
    cB
    cc0
    wceq
    wa
    #
    wn
    cA
    cc0
    wne
    cB
    cc0
    wne
    wo
    @0
    @2
    @1
    cc0
    @1
    cc0
    wceq
    @1
    cc0
    ci
    cc0
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @0
    @2
    @4
    cc0
    @1
    @4
    cc0
    cc0
    caddc
    co
    cc0
    @3
    cc0
    cc0
    caddc
    ci
    ax-icn
    mul01i
    oveq2i
    00id
    eqtri
    eqeq2i
    @0
    cc0
    cr
    wcel
    #
    @6
    @5
    @2
    wb
    0re
    0re
    cA
    cB
    cc0
    cc0
    cru
    mpanr12
    syl5bbr
    necon3abid
    cA
    cc0
    cB
    cc0
    neorian
    syl6rbbr
end
