include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wt.mm"
include "comor1.mm"
include "comcom7.mm"
include "comor2.mm"
include "fh4c.mm"
include "df-t.mm"
include "ax-r5.mm"
include "ax-a2.mm"
include "or1.mm"
include "ax-r2.mm"
include "ax-a3.mm"
include "3tr2.mm"
include "ax-r1.mm"
include "lan.mm"
include "an1.mm"
include "3tr.mm"

theorem oml6
  param wva: term a
  param wvb: term b


  assert |- ( a v ( b ^ ( a ' v b ' ) ) ) = ( a v b )

  proof
    wva
    wvb
    wva
    wn
    #
    wvb
    wn
    #
    wo
    #
    wa
    wo
    wva
    wvb
    wo
    #
    wva
    @2
    wo
    #
    wa
    @3
    wt
    wa
    @3
    @2
    wva
    wvb
    @2
    wva
    @0
    @1
    comor1
    comcom7
    @2
    wvb
    @0
    @1
    comor2
    comcom7
    fh4c
    @4
    wt
    @3
    wt
    @4
    wt
    @1
    wo
    #
    wva
    @0
    wo
    #
    @1
    wo
    wt
    @4
    wt
    @6
    @1
    wva
    df-t
    ax-r5
    @5
    @1
    wt
    wo
    wt
    wt
    @1
    ax-a2
    @1
    or1
    ax-r2
    wva
    @0
    @1
    ax-a3
    3tr2
    ax-r1
    lan
    @3
    an1
    3tr
end
