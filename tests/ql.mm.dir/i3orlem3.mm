include "wo.mm"
include "wn.mm"
include "wa.mm"
include "wi3.mm"
include "ax-a2.mm"
include "lan.mm"
include "anabs.mm"
include "ax-r2.mm"
include "ax-r1.mm"
include "leor.mm"
include "lelor.mm"
include "le2an.mm"
include "bltr.mm"
include "i3orlem1.mm"
include "letr.mm"

theorem i3orlem3
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- c =< ( ( a v c ) ->3 ( b v c ) )

  proof
    wvc
    wva
    wvc
    wo
    #
    @0
    wn
    #
    wvb
    wvc
    wo
    #
    wo
    #
    wa
    #
    @0
    @2
    wi3
    wvc
    wvc
    @1
    wvc
    wo
    #
    wa
    #
    @4
    @6
    wvc
    @6
    wvc
    wvc
    @1
    wo
    #
    wa
    wvc
    @5
    @7
    wvc
    @1
    wvc
    ax-a2
    lan
    wvc
    @1
    anabs
    ax-r2
    ax-r1
    wvc
    @0
    @5
    @3
    wvc
    wva
    leor
    wvc
    @2
    @1
    wvc
    wvb
    leor
    lelor
    le2an
    bltr
    wva
    wvb
    wvc
    i3orlem1
    letr
end
