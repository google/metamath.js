include "wa.mm"
include "wn.mm"
include "wo.mm"
include "lea.mm"
include "lel2or.mm"
include "df-le2.mm"
include "wt.mm"
include "le1.mm"
include "wcmtr.mm"
include "df-cmtr.mm"
include "ax-a2.mm"
include "3tr2.mm"
include "leror.mm"
include "bltr.mm"
include "lebi.mm"
include "lem3.1.mm"
include "ax-r1.mm"
include "df-c1.mm"

theorem cmtr1com
  let wva: term a
  let wvb: term b
  assume cmtr1com.1: |- C ( a , b ) = 1


  assert |- a C b

  proof
    wva
    wvb
    wva
    wvb
    wa
    #
    wva
    wvb
    wn
    #
    wa
    #
    wo
    #
    wva
    @3
    wva
    @3
    wva
    @0
    wva
    @2
    wva
    wvb
    lea
    wva
    @1
    lea
    lel2or
    df-le2
    wva
    wn
    #
    @3
    wo
    #
    wt
    @5
    le1
    wt
    @4
    wvb
    wa
    #
    @4
    @1
    wa
    #
    wo
    #
    @3
    wo
    #
    @5
    wva
    wvb
    wcmtr
    @3
    @8
    wo
    wt
    @9
    wva
    wvb
    df-cmtr
    cmtr1com.1
    @3
    @8
    ax-a2
    3tr2
    @8
    @4
    @3
    @6
    @4
    @7
    @4
    wvb
    lea
    @4
    @1
    lea
    lel2or
    leror
    bltr
    lebi
    lem3.1
    ax-r1
    df-c1
end
