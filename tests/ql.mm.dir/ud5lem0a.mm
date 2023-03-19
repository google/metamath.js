include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi5.mm"
include "lan.mm"
include "2or.mm"
include "ax-r4.mm"
include "df-i5.mm"
include "3tr1.mm"

theorem ud5lem0a
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume ud5lem0a.1: |- a = b


  assert |- ( c ->5 a ) = ( c ->5 b )

  proof
    wvc
    wva
    wa
    #
    wvc
    wn
    #
    wva
    wa
    #
    wo
    #
    @1
    wva
    wn
    #
    wa
    #
    wo
    wvc
    wvb
    wa
    #
    @1
    wvb
    wa
    #
    wo
    #
    @1
    wvb
    wn
    #
    wa
    #
    wo
    wvc
    wva
    wi5
    wvc
    wvb
    wi5
    @3
    @8
    @5
    @10
    @0
    @6
    @2
    @7
    wva
    wvb
    wvc
    ud5lem0a.1
    lan
    wva
    wvb
    @1
    ud5lem0a.1
    lan
    2or
    @4
    @9
    @1
    wva
    wvb
    ud5lem0a.1
    ax-r4
    lan
    2or
    wvc
    wva
    df-i5
    wvc
    wvb
    df-i5
    3tr1
end
