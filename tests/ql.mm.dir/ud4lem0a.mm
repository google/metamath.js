include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi4.mm"
include "lan.mm"
include "2or.mm"
include "lor.mm"
include "ax-r4.mm"
include "2an.mm"
include "df-i4.mm"
include "3tr1.mm"

theorem ud4lem0a
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume ud4lem0a.1: |- a = b


  assert |- ( c ->4 a ) = ( c ->4 b )

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
    wo
    #
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
    wo
    #
    wvb
    wn
    #
    wa
    #
    wo
    wvc
    wva
    wi4
    wvc
    wvb
    wi4
    @3
    @9
    @6
    @12
    @0
    @7
    @2
    @8
    wva
    wvb
    wvc
    ud4lem0a.1
    lan
    wva
    wvb
    @1
    ud4lem0a.1
    lan
    2or
    @4
    @10
    @5
    @11
    wva
    wvb
    @1
    ud4lem0a.1
    lor
    wva
    wvb
    ud4lem0a.1
    ax-r4
    2an
    2or
    wvc
    wva
    df-i4
    wvc
    wvb
    df-i4
    3tr1
end
