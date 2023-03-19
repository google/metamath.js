include "wn.mm"
include "wa.mm"
include "wo.mm"
include "orabs.mm"
include "ax-r1.mm"
include "df2le2.mm"
include "ax-r5.mm"
include "ax-r2.mm"
include "df-c1.mm"

theorem lecom
  param wva: term a
  param wvb: term b
  assume lecom.1: |- a =< b


  assert |- a C b

  proof
    wva
    wvb
    wva
    wva
    wva
    wvb
    wn
    #
    wa
    #
    wo
    #
    wva
    wvb
    wa
    #
    @1
    wo
    @2
    wva
    wva
    @0
    orabs
    ax-r1
    wva
    @3
    @1
    @3
    wva
    wva
    wvb
    lecom.1
    df2le2
    ax-r1
    ax-r5
    ax-r2
    df-c1
end
