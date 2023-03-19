include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wcomcom4.mm"
include "wdf-c2.mm"
include "wcon3.mm"
include "oran.mm"
include "bi1.mm"
include "wcon2.mm"
include "w2an.mm"
include "wr1.mm"
include "wr2.mm"

theorem wcomd
  param wva: term a
  param wvb: term b
  assume wcomcom.1: |- C ( a , b ) = 1


  assert |- ( a == ( ( a v b ) ^ ( a v b ' ) ) ) = 1

  proof
    wva
    wva
    wn
    #
    wvb
    wn
    #
    wa
    #
    @0
    @1
    wn
    wa
    #
    wo
    #
    wn
    #
    wva
    wvb
    wo
    #
    wva
    @1
    wo
    #
    wa
    #
    wva
    @4
    @0
    @1
    wva
    wvb
    wcomcom.1
    wcomcom4
    wdf-c2
    wcon3
    @5
    @2
    wn
    #
    @3
    wn
    #
    wa
    #
    @8
    @4
    @11
    @4
    @11
    wn
    @2
    @3
    oran
    bi1
    wcon2
    @8
    @11
    @6
    @9
    @7
    @10
    @6
    @9
    wva
    wvb
    oran
    bi1
    @7
    @10
    wva
    @1
    oran
    bi1
    w2an
    wr1
    wr2
    wr2
end
