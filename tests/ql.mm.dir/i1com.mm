include "wi1.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "ancom.mm"
include "df2le2.mm"
include "u1lemab.mm"
include "2or.mm"
include "ax-r2.mm"
include "3tr2.mm"
include "df-c1.mm"
include "comcom.mm"

theorem i1com
  param wva: term a
  param wvb: term b
  assume i1com.1: |- b =< ( a ->1 b )


  assert |- a C b

  proof
    wvb
    wva
    wvb
    wva
    wvb
    wva
    wvb
    wi1
    #
    wa
    @0
    wvb
    wa
    #
    wvb
    wvb
    wva
    wa
    #
    wvb
    wva
    wn
    #
    wa
    #
    wo
    #
    wvb
    @0
    ancom
    wvb
    @0
    i1com.1
    df2le2
    @1
    wva
    wvb
    wa
    #
    @3
    wvb
    wa
    #
    wo
    @5
    wva
    wvb
    u1lemab
    @6
    @2
    @7
    @4
    wva
    wvb
    ancom
    @3
    wvb
    ancom
    2or
    ax-r2
    3tr2
    df-c1
    comcom
end
