include "wt.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "df-a.mm"
include "wf.mm"
include "df-f.mm"
include "ax-r1.mm"
include "lor.mm"
include "or0.mm"
include "ax-r2.mm"
include "con2.mm"

theorem an1
  let wva: term a


  assert |- ( a ^ 1 ) = a

  proof
    wva
    wt
    wa
    wva
    wn
    #
    wt
    wn
    #
    wo
    #
    wn
    wva
    wva
    wt
    df-a
    @2
    wva
    @2
    @0
    wf
    wo
    @0
    @1
    wf
    @0
    wf
    @1
    df-f
    ax-r1
    lor
    @0
    or0
    ax-r2
    con2
    ax-r2
end
