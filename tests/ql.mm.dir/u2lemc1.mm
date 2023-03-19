include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi2.mm"
include "comid.mm"
include "comanr2.mm"
include "comcom6.mm"
include "com2or.mm"
include "df-i2.mm"
include "ax-r1.mm"
include "cbtr.mm"

theorem u2lemc1
  param wva: term a
  param wvb: term b


  assert |- b C ( a ->2 b )

  proof
    wvb
    wvb
    wva
    wn
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    wva
    wvb
    wi2
    #
    wvb
    wvb
    @2
    wvb
    comid
    wvb
    @2
    @0
    @1
    comanr2
    comcom6
    com2or
    @4
    @3
    wva
    wvb
    df-i2
    ax-r1
    cbtr
end
