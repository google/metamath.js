include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wcomcom.mm"
include "wcomd.mm"
include "wlan.mm"
include "anass.mm"
include "bi1.mm"
include "wr1.mm"
include "ax-a2.mm"
include "anabs.mm"
include "wr2.mm"
include "w2an.mm"

theorem wcom3ii
  param wva: term a
  param wvb: term b
  assume wcomcom.1: |- C ( a , b ) = 1


  assert |- ( ( a ^ ( a ' v b ) ) == ( a ^ b ) ) = 1

  proof
    wva
    wvb
    wa
    #
    wva
    wva
    wn
    #
    wvb
    wo
    #
    wa
    #
    @0
    wva
    wvb
    wva
    wo
    #
    wvb
    @1
    wo
    #
    wa
    #
    wa
    #
    @3
    wvb
    @6
    wva
    wvb
    wva
    wva
    wvb
    wcomcom.1
    wcomcom
    wcomd
    wlan
    @7
    wva
    @4
    wa
    #
    @5
    wa
    #
    @3
    @9
    @7
    @9
    @7
    wva
    @4
    @5
    anass
    bi1
    wr1
    @8
    wva
    @5
    @2
    @8
    wva
    wva
    wvb
    wo
    #
    wa
    #
    wva
    @4
    @10
    wva
    @4
    @10
    wvb
    wva
    ax-a2
    bi1
    wlan
    @11
    wva
    wva
    wvb
    anabs
    bi1
    wr2
    @5
    @2
    wvb
    @1
    ax-a2
    bi1
    w2an
    wr2
    wr2
    wr1
end
