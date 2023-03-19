include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi4.mm"
include "comanr2.mm"
include "com2or.mm"
include "comorr2.mm"
include "comid.mm"
include "comcom2.mm"
include "com2an.mm"
include "df-i4.mm"
include "ax-r1.mm"
include "cbtr.mm"

theorem u4lemc1
  let wva: term a
  let wvb: term b


  assert |- b C ( a ->4 b )

  proof
    wvb
    wva
    wvb
    wa
    #
    wva
    wn
    #
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
    #
    wva
    wvb
    wi4
    #
    wvb
    @3
    @6
    wvb
    @0
    @2
    wva
    wvb
    comanr2
    @1
    wvb
    comanr2
    com2or
    wvb
    @4
    @5
    @1
    wvb
    comorr2
    wvb
    wvb
    wvb
    comid
    comcom2
    com2an
    com2or
    @8
    @7
    wva
    wvb
    df-i4
    ax-r1
    cbtr
end
