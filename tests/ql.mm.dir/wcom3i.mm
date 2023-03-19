include "wn.mm"
include "wa.mm"
include "wo.mm"
include "anor1.mm"
include "bi1.mm"
include "wcon2.mm"
include "wran.mm"
include "ancom.mm"
include "wr2.mm"
include "wlor.mm"
include "wlea.mm"
include "wom4.mm"
include "ax-a2.mm"
include "w3tr2.mm"
include "wdf-c1.mm"

theorem wcom3i
  let wva: term a
  let wvb: term b
  assume wcom3i.1: |- ( ( a ^ ( a ' v b ) ) == ( a ^ b ) ) = 1


  assert |- C ( a , b ) = 1

  proof
    wva
    wvb
    wva
    wvb
    wn
    #
    wa
    #
    @1
    wn
    #
    wva
    wa
    #
    wo
    @1
    wva
    wvb
    wa
    #
    wo
    #
    wva
    @4
    @1
    wo
    #
    @3
    @4
    @1
    @3
    wva
    wva
    wn
    wvb
    wo
    #
    wa
    #
    @4
    @3
    @7
    wva
    wa
    #
    @8
    @2
    @7
    wva
    @1
    @7
    @1
    @7
    wn
    wva
    wvb
    anor1
    bi1
    wcon2
    wran
    @9
    @8
    @7
    wva
    ancom
    bi1
    wr2
    wcom3i.1
    wr2
    wlor
    @1
    wva
    wva
    @0
    wlea
    wom4
    @5
    @6
    @1
    @4
    ax-a2
    bi1
    w3tr2
    wdf-c1
end
