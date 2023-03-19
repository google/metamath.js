include "wi1.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wt.mm"
include "df-i1.mm"
include "ax-a1.mm"
include "ax-r5.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "lor.mm"
include "orordi.mm"
include "u1lemoa.mm"
include "or1r.mm"

theorem i1orni1
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->1 b ) v ( a ' ->1 b ) ) = 1

  proof
    wva
    wvb
    wi1
    #
    wva
    wn
    #
    wvb
    wi1
    #
    wo
    @0
    wva
    @1
    wvb
    wa
    #
    wo
    #
    wo
    #
    wt
    @2
    @4
    @0
    @2
    @1
    wn
    #
    @3
    wo
    #
    @4
    @1
    wvb
    df-i1
    @4
    @7
    wva
    @6
    @3
    wva
    ax-a1
    ax-r5
    ax-r1
    ax-r2
    lor
    @5
    @0
    wva
    wo
    #
    @0
    @3
    wo
    #
    wo
    #
    wt
    @0
    wva
    @3
    orordi
    @10
    wt
    @9
    wo
    wt
    @8
    wt
    @9
    wva
    wvb
    u1lemoa
    ax-r5
    @9
    or1r
    ax-r2
    ax-r2
    ax-r2
end
