include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wt.mm"
include "df-t.mm"
include "ax-r1.mm"
include "ax-a2.mm"
include "bi1.mm"
include "wwbmpr.mm"
include "wlan.mm"
include "anidm.mm"
include "wr1.mm"
include "wleo.mm"
include "wle2an.mm"
include "wbltr.mm"
include "wlecom.mm"
include "wcomcom3.mm"
include "wcomcom4.mm"
include "wfh1.mm"
include "an1.mm"
include "w3tr2.mm"
include "wlor.mm"

theorem wlem14
  let wva: term a
  let wvb: term b


  assert |- ( ( ( a ^ b ' ) v a ' ) ' v ( ( a ^ b ' ) v ( ( a ' ^ ( ( a v b ' ) ^ ( a v b ) ) ) v ( a ' ^ ( ( a v b ' ) ^ ( a v b ) ) ' ) ) ) ) = 1

  proof
    wva
    wvb
    wn
    #
    wa
    #
    wva
    wn
    #
    wo
    #
    wn
    #
    @1
    @2
    wva
    @0
    wo
    #
    wva
    wvb
    wo
    #
    wa
    #
    wa
    @2
    @7
    wn
    #
    wa
    wo
    #
    wo
    #
    wo
    @4
    @3
    wo
    #
    @11
    @3
    @4
    wo
    #
    wt
    @12
    @3
    df-t
    ax-r1
    @11
    @12
    @4
    @3
    ax-a2
    bi1
    wwbmpr
    @10
    @3
    @4
    @9
    @2
    @1
    @2
    @7
    @8
    wo
    #
    wa
    @2
    wt
    wa
    #
    @9
    @2
    @13
    wt
    @2
    @13
    wt
    wt
    @13
    @7
    df-t
    ax-r1
    bi1
    wlan
    @2
    @7
    @8
    wva
    @7
    wva
    @7
    wva
    wva
    wva
    wa
    #
    @7
    @15
    wva
    @15
    wva
    wva
    anidm
    bi1
    wr1
    wva
    @5
    wva
    @6
    wva
    @0
    wleo
    wva
    wvb
    wleo
    wle2an
    wbltr
    wlecom
    #
    wcomcom3
    wva
    @7
    @16
    wcomcom4
    wfh1
    @14
    @2
    @2
    an1
    bi1
    w3tr2
    wlor
    wlor
    wwbmpr
end
