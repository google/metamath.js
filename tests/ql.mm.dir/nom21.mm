include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wid1.mm"
include "wi1.mm"
include "ancom.mm"
include "or12.mm"
include "oran3.mm"
include "lor.mm"
include "ax-r2.mm"
include "anidm.mm"
include "ran.mm"
include "ax-r1.mm"
include "anass.mm"
include "2an.mm"
include "lea.mm"
include "leo.mm"
include "letr.mm"
include "lelor.mm"
include "df2le2.mm"
include "3tr2.mm"
include "df-id1.mm"
include "df-i1.mm"
include "3tr1.mm"

theorem nom21
  let wva: term a
  let wvb: term b


  assert |- ( a ==1 ( a ^ b ) ) = ( a ->1 b )

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
    wva
    wn
    #
    wva
    @0
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
    wid1
    wva
    wvb
    wi1
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
    @6
    @7
    @10
    @7
    ancom
    @10
    @2
    @7
    @5
    @10
    wva
    @3
    @8
    wo
    #
    wo
    @2
    @3
    wva
    @8
    or12
    @11
    @1
    wva
    wva
    wvb
    oran3
    lor
    ax-r2
    @0
    @4
    @3
    @0
    wva
    wva
    wa
    #
    wvb
    wa
    #
    @4
    @13
    @0
    @12
    wva
    wvb
    wva
    anidm
    ran
    ax-r1
    wva
    wva
    wvb
    anass
    ax-r2
    lor
    2an
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
    3tr2
    wva
    @0
    df-id1
    wva
    wvb
    df-i1
    3tr1
end
