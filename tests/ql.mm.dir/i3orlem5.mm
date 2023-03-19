include "wo.mm"
include "wn.mm"
include "wa.mm"
include "wi3.mm"
include "leo.mm"
include "anandir.mm"
include "oran.mm"
include "con2.mm"
include "ax-r1.mm"
include "2an.mm"
include "ax-r2.mm"
include "df2i3.mm"
include "le3tr1.mm"

theorem i3orlem5
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a ' ^ b ' ) ^ c ' ) =< ( ( a v c ) ->3 ( b v c ) )

  proof
    wva
    wvc
    wo
    #
    wn
    #
    wvb
    wvc
    wo
    #
    wn
    #
    wa
    #
    @4
    @1
    @2
    wo
    @0
    @1
    @2
    wa
    wo
    wa
    #
    wo
    wva
    wn
    #
    wvb
    wn
    #
    wa
    wvc
    wn
    #
    wa
    #
    @0
    @2
    wi3
    @4
    @5
    leo
    @9
    @6
    @8
    wa
    #
    @7
    @8
    wa
    #
    wa
    @4
    @6
    @7
    @8
    anandir
    @10
    @1
    @11
    @3
    @1
    @10
    @0
    @10
    wva
    wvc
    oran
    con2
    ax-r1
    @3
    @11
    @2
    @11
    wvb
    wvc
    oran
    con2
    ax-r1
    2an
    ax-r2
    @0
    @2
    df2i3
    le3tr1
end
