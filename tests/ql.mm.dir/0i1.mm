include "wf.mm"
include "wi1.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wt.mm"
include "df-i1.mm"
include "ax-a2.mm"
include "df-f.mm"
include "con2.mm"
include "lor.mm"
include "ax-r2.mm"
include "or1.mm"
include "3tr.mm"

theorem 0i1
  let wva: term a


  assert |- ( 0 ->1 a ) = 1

  proof
    wf
    wva
    wi1
    wf
    wn
    #
    wf
    wva
    wa
    #
    wo
    #
    @1
    wt
    wo
    #
    wt
    wf
    wva
    df-i1
    @2
    @1
    @0
    wo
    @3
    @0
    @1
    ax-a2
    @0
    wt
    @1
    wf
    wt
    df-f
    con2
    lor
    ax-r2
    @1
    or1
    3tr
end
