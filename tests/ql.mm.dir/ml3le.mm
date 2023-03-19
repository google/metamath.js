include "wo.mm"
include "wa.mm"
include "lear.mm"
include "lelor.mm"
include "or12.mm"
include "oridm.mm"
include "lor.mm"
include "orcom.mm"
include "3tr.mm"
include "lbtr.mm"
include "leor.mm"
include "leao1.mm"
include "lel2or.mm"
include "ler2an.mm"
include "mlduali.mm"

theorem ml3le
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( a v ( b ^ ( c v a ) ) ) =< ( a v ( c ^ ( b v a ) ) )

  proof
    wva
    wvb
    wvc
    wva
    wo
    #
    wa
    #
    wo
    #
    wva
    wvc
    wo
    #
    wvb
    wva
    wo
    #
    wa
    wva
    wvc
    @4
    wa
    wo
    @2
    @3
    @4
    @2
    wva
    @0
    wo
    #
    @3
    @1
    @0
    wva
    wvb
    @0
    lear
    lelor
    @5
    wvc
    wva
    wva
    wo
    #
    wo
    @0
    @3
    wva
    wvc
    wva
    or12
    @6
    wva
    wvc
    wva
    oridm
    lor
    wvc
    wva
    orcom
    3tr
    lbtr
    wva
    @4
    @1
    wva
    wvb
    leor
    #
    wvb
    @0
    wva
    leao1
    lel2or
    ler2an
    wva
    wvc
    @4
    @7
    mlduali
    lbtr
end
