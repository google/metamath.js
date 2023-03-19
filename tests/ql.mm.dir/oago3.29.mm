include "wi1.mm"
include "wi2.mm"
include "wa.mm"
include "tb.mm"
include "wt.mm"
include "anass.mm"
include "i2id.mm"
include "2an.mm"
include "ax-r1.mm"
include "an1.mm"
include "mhcor1.mm"
include "3tr2.mm"
include "lear.mm"
include "bicom.mm"
include "lbtr.mm"
include "bltr.mm"

theorem oago3.29
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a ->1 b ) ^ ( ( b ->2 c ) ^ ( c ->1 a ) ) ) =< ( a == c )

  proof
    wva
    wvb
    wi1
    #
    wvb
    wvc
    wi2
    #
    wvc
    wva
    wi1
    #
    wa
    wa
    #
    wva
    wvb
    tb
    wvb
    wvc
    tb
    wa
    #
    wvc
    wva
    tb
    #
    wa
    #
    wva
    wvc
    tb
    #
    @3
    wt
    wa
    #
    @0
    @1
    wa
    @2
    wa
    #
    wva
    wva
    wi2
    #
    wa
    #
    @3
    @6
    @11
    @8
    @9
    @3
    @10
    wt
    @0
    @1
    @2
    anass
    wva
    i2id
    2an
    ax-r1
    @3
    an1
    wva
    wvb
    wvc
    wva
    mhcor1
    3tr2
    @6
    @5
    @7
    @4
    @5
    lear
    wvc
    wva
    bicom
    lbtr
    bltr
end
