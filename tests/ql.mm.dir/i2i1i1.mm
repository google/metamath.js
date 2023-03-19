include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wt.mm"
include "wi2.mm"
include "wi1.mm"
include "an1r.mm"
include "ax-r1.mm"
include "df-i2.mm"
include "anabs.mm"
include "lor.mm"
include "ax-a2.mm"
include "ax-r2.mm"
include "df-i1.mm"
include "df-t.mm"
include "3tr1.mm"
include "anor3.mm"
include "leor.mm"
include "leid.mm"
include "ler2an.mm"
include "lear.mm"
include "lebi.mm"
include "2or.mm"
include "3tr.mm"
include "2an.mm"

theorem i2i1i1
  param wva: term a
  param wvb: term b


  assert |- ( a ->2 b ) = ( ( a ->1 ( a v b ) ) ^ ( ( a v b ) ->1 b ) )

  proof
    wvb
    wva
    wn
    #
    wvb
    wn
    wa
    #
    wo
    #
    wt
    @2
    wa
    #
    wva
    wvb
    wi2
    wva
    wva
    wvb
    wo
    #
    wi1
    #
    @4
    wvb
    wi1
    #
    wa
    @3
    @2
    @2
    an1r
    ax-r1
    wva
    wvb
    df-i2
    @5
    wt
    @6
    @2
    @0
    wva
    @4
    wa
    #
    wo
    #
    wva
    @0
    wo
    #
    @5
    wt
    @8
    @0
    wva
    wo
    @9
    @7
    wva
    @0
    wva
    wvb
    anabs
    lor
    @0
    wva
    ax-a2
    ax-r2
    wva
    @4
    df-i1
    wva
    df-t
    3tr1
    @6
    @4
    wn
    #
    @4
    wvb
    wa
    #
    wo
    #
    @1
    wvb
    wo
    #
    @2
    @4
    wvb
    df-i1
    @13
    @12
    @1
    @10
    wvb
    @11
    wva
    wvb
    anor3
    wvb
    @11
    wvb
    @4
    wvb
    wvb
    wva
    leor
    wvb
    leid
    ler2an
    @4
    wvb
    lear
    lebi
    2or
    ax-r1
    @1
    wvb
    ax-a2
    3tr
    2an
    3tr1
end
