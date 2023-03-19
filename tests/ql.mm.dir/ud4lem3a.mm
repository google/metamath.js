include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wi4.mm"
include "anass.mm"
include "lea.mm"
include "leror.mm"
include "df2le2.mm"
include "lan.mm"
include "ax-r2.mm"
include "ud4lem0c.mm"
include "ran.mm"
include "3tr1.mm"

theorem ud4lem3a
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->4 b ) ' ^ ( a v b ) ) = ( a ->4 b ) '

  proof
    wva
    wn
    wvb
    wn
    #
    wo
    wva
    @0
    wo
    wa
    #
    wva
    @0
    wa
    #
    wvb
    wo
    #
    wa
    #
    wva
    wvb
    wo
    #
    wa
    #
    @4
    wva
    wvb
    wi4
    wn
    #
    @5
    wa
    @7
    @6
    @1
    @3
    @5
    wa
    #
    wa
    @4
    @1
    @3
    @5
    anass
    @8
    @3
    @1
    @3
    @5
    @2
    wva
    wvb
    wva
    @0
    lea
    leror
    df2le2
    lan
    ax-r2
    @7
    @4
    @5
    wva
    wvb
    ud4lem0c
    #
    ran
    @9
    3tr1
end
