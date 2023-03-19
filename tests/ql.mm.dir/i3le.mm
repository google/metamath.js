include "wn.mm"
include "wt.mm"
include "wa.mm"
include "ancom.mm"
include "wo.mm"
include "i3lem3.mm"
include "i3lem4.mm"
include "ran.mm"
include "3tr2.mm"
include "an1.mm"
include "df2le1.mm"
include "lecon1.mm"

theorem i3le
  param wva: term a
  param wvb: term b
  assume i3le.1: |- ( a ->3 b ) = 1


  assert |- a =< b

  proof
    wvb
    wva
    wvb
    wn
    #
    wva
    wn
    #
    wt
    @0
    wa
    #
    @0
    wt
    wa
    @0
    @1
    wa
    #
    @0
    wt
    @0
    ancom
    @1
    wvb
    wo
    #
    @0
    wa
    @1
    @0
    wa
    @2
    @3
    wva
    wvb
    i3le.1
    i3lem3
    @4
    wt
    @0
    wva
    wvb
    i3le.1
    i3lem4
    ran
    @1
    @0
    ancom
    3tr2
    @0
    an1
    3tr2
    df2le1
    lecon1
end
