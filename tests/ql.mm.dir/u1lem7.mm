include "wn.mm"
include "wi1.mm"
include "wa.mm"
include "wo.mm"
include "wt.mm"
include "df-i1.mm"
include "ax-a1.mm"
include "ran.mm"
include "ancom.mm"
include "u1lemana.mm"
include "ax-r2.mm"
include "lor.mm"
include "df-t.mm"
include "ax-r1.mm"

theorem u1lem7
  let wva: term a
  let wvb: term b


  assert |- ( a ->1 ( a ' ->1 b ) ) = 1

  proof
    wva
    wva
    wn
    #
    wvb
    wi1
    #
    wi1
    @0
    wva
    @1
    wa
    #
    wo
    #
    wt
    wva
    @1
    df-i1
    @3
    @0
    @0
    wn
    #
    wo
    #
    wt
    @2
    @4
    @0
    @2
    @4
    @1
    wa
    #
    @4
    wva
    @4
    @1
    wva
    ax-a1
    ran
    @6
    @1
    @4
    wa
    @4
    @4
    @1
    ancom
    @0
    wvb
    u1lemana
    ax-r2
    ax-r2
    lor
    wt
    @5
    @0
    df-t
    ax-r1
    ax-r2
    ax-r2
end
