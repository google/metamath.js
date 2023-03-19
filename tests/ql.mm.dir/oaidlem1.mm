include "wn.mm"
include "wi1.mm"
include "wo.mm"
include "wa.mm"
include "wt.mm"
include "df-i1.mm"
include "lor.mm"
include "oran3.mm"
include "ax-r5.mm"
include "ax-a3.mm"
include "lear.mm"
include "ler2an.mm"
include "sklem.mm"
include "3tr2.mm"
include "ax-r2.mm"

theorem oaidlem1
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume oaidlem1.1: |- ( a ^ b ) =< c


  assert |- ( a ' v ( b ->1 c ) ) = 1

  proof
    wva
    wn
    #
    wvb
    wvc
    wi1
    #
    wo
    @0
    wvb
    wn
    #
    wvb
    wvc
    wa
    #
    wo
    #
    wo
    #
    wt
    @1
    @4
    @0
    wvb
    wvc
    df-i1
    lor
    @0
    @2
    wo
    #
    @3
    wo
    wva
    wvb
    wa
    #
    wn
    #
    @3
    wo
    @5
    wt
    @6
    @8
    @3
    wva
    wvb
    oran3
    ax-r5
    @0
    @2
    @3
    ax-a3
    @7
    @3
    @7
    wvb
    wvc
    wva
    wvb
    lear
    oaidlem1.1
    ler2an
    sklem
    3tr2
    ax-r2
end
