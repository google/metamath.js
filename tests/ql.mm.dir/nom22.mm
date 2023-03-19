include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wid2.mm"
include "wi1.mm"
include "oran3.mm"
include "lor.mm"
include "ax-r1.mm"
include "or12.mm"
include "ax-r2.mm"
include "ax-a2.mm"
include "lan.mm"
include "anabs.mm"
include "ax-r5.mm"
include "2an.mm"
include "ancom.mm"
include "lea.mm"
include "leo.mm"
include "letr.mm"
include "lelor.mm"
include "df2le2.mm"
include "3tr.mm"
include "df-id2.mm"
include "df-i1.mm"
include "3tr1.mm"

theorem nom22
  let wva: term a
  let wvb: term b


  assert |- ( a ==2 ( a ^ b ) ) = ( a ->1 b )

  proof
    wva
    wva
    wvb
    wa
    #
    wn
    #
    wo
    #
    @0
    wva
    wn
    #
    @1
    wa
    #
    wo
    #
    wa
    #
    @3
    @0
    wo
    #
    wva
    @0
    wid2
    wva
    wvb
    wi1
    @6
    @3
    wva
    wvb
    wn
    #
    wo
    #
    wo
    #
    @7
    wa
    @7
    @10
    wa
    @7
    @2
    @10
    @5
    @7
    @2
    wva
    @3
    @8
    wo
    #
    wo
    #
    @10
    @12
    @2
    @11
    @1
    wva
    wva
    wvb
    oran3
    #
    lor
    ax-r1
    wva
    @3
    @8
    or12
    ax-r2
    @5
    @4
    @0
    wo
    @7
    @0
    @4
    ax-a2
    @4
    @3
    @0
    @4
    @3
    @11
    wa
    #
    @3
    @14
    @4
    @11
    @1
    @3
    @13
    lan
    ax-r1
    @3
    @8
    anabs
    ax-r2
    ax-r5
    ax-r2
    2an
    @10
    @7
    ancom
    @7
    @10
    @0
    @9
    @3
    @0
    wva
    @9
    wva
    wvb
    lea
    wva
    @8
    leo
    letr
    lelor
    df2le2
    3tr
    wva
    @0
    df-id2
    wva
    wvb
    df-i1
    3tr1
end
