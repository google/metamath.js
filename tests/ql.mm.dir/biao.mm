include "wa.mm"
include "wn.mm"
include "wo.mm"
include "tb.mm"
include "leao1.mm"
include "df2le2.mm"
include "ax-r1.mm"
include "anor3.mm"
include "lecon.mm"
include "oridm.mm"
include "df-le1.mm"
include "ler2an.mm"
include "lear.mm"
include "df-le2.mm"
include "lebi.mm"
include "ax-r2.mm"
include "2or.mm"
include "dfb.mm"
include "3tr1.mm"

theorem biao
  param wva: term a
  param wvb: term b


  assert |- ( a == b ) = ( ( a ^ b ) == ( a v b ) )

  proof
    wva
    wvb
    wa
    #
    wva
    wn
    wvb
    wn
    wa
    #
    wo
    @0
    wva
    wvb
    wo
    #
    wa
    #
    @0
    wn
    #
    @2
    wn
    #
    wa
    #
    wo
    wva
    wvb
    tb
    @0
    @2
    tb
    @0
    @3
    @1
    @6
    @3
    @0
    @0
    @2
    wva
    wvb
    wvb
    leao1
    #
    df2le2
    ax-r1
    @1
    @5
    @6
    wva
    wvb
    anor3
    @5
    @6
    @5
    @4
    @5
    @0
    @2
    @7
    lecon
    @5
    @5
    @5
    oridm
    df-le1
    ler2an
    @6
    @5
    @6
    @5
    @4
    @5
    lear
    df-le2
    df-le1
    lebi
    ax-r2
    2or
    wva
    wvb
    dfb
    @0
    @2
    dfb
    3tr1
end
