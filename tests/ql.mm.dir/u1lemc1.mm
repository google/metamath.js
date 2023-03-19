include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi1.mm"
include "comid.mm"
include "comcom2.mm"
include "comanr1.mm"
include "com2or.mm"
include "df-i1.mm"
include "ax-r1.mm"
include "cbtr.mm"

theorem u1lemc1
  let wva: term a
  let wvb: term b


  assert |- a C ( a ->1 b )

  proof
    wva
    wva
    wn
    #
    wva
    wvb
    wa
    #
    wo
    #
    wva
    wvb
    wi1
    #
    wva
    @0
    @1
    wva
    wva
    wva
    comid
    comcom2
    wva
    wvb
    comanr1
    com2or
    @3
    @2
    wva
    wvb
    df-i1
    ax-r1
    cbtr
end
