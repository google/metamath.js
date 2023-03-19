include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi1.mm"
include "wi2.mm"
include "ax-a1.mm"
include "2an.mm"
include "ancom.mm"
include "ax-r2.mm"
include "lor.mm"
include "df-i1.mm"
include "df-i2.mm"
include "3tr1.mm"

theorem i1i2
  param wva: term a
  param wvb: term b


  assert |- ( a ->1 b ) = ( b ' ->2 a ' )

  proof
    wva
    wn
    #
    wva
    wvb
    wa
    #
    wo
    @0
    wvb
    wn
    #
    wn
    #
    @0
    wn
    #
    wa
    #
    wo
    wva
    wvb
    wi1
    @2
    @0
    wi2
    @1
    @5
    @0
    @1
    @4
    @3
    wa
    @5
    wva
    @4
    wvb
    @3
    wva
    ax-a1
    wvb
    ax-a1
    2an
    @4
    @3
    ancom
    ax-r2
    lor
    wva
    wvb
    df-i1
    @2
    @0
    df-i2
    3tr1
end
