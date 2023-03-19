include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "axlttri.mm"
include "pm2.46.mm"
include "syl6bi.mm"

theorem ltnsym
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < B -> -. B < A ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    wa
    cA
    cB
    clt
    wbr
    cA
    cB
    wceq
    #
    cB
    cA
    clt
    wbr
    #
    wo
    wn
    @1
    wn
    cA
    cB
    axlttri
    @0
    @1
    pm2.46
    syl6bi
end
