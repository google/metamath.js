include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi4.mm"
include "wi1.mm"
include "ax-a2.mm"
include "anass.mm"
include "ax-r1.mm"
include "anidm.mm"
include "ran.mm"
include "ax-r2.mm"
include "lor.mm"
include "lear.mm"
include "df-le2.mm"
include "3tr.mm"
include "ax-r5.mm"
include "leo.mm"
include "lea.mm"
include "lbtr.mm"
include "lel2or.mm"
include "lecon.mm"
include "ler2an.mm"
include "lelor.mm"
include "lebi.mm"
include "df-i4.mm"
include "df-i1.mm"
include "3tr1.mm"

theorem nom14
  param wva: term a
  param wvb: term b


  assert |- ( a ->4 ( a ^ b ) ) = ( a ->1 b )

  proof
    wva
    wva
    wvb
    wa
    #
    wa
    #
    wva
    wn
    #
    @0
    wa
    #
    wo
    #
    @2
    @0
    wo
    #
    @0
    wn
    #
    wa
    #
    wo
    #
    @5
    wva
    @0
    wi4
    wva
    wvb
    wi1
    @8
    @0
    @7
    wo
    #
    @0
    @2
    wo
    #
    @5
    @4
    @0
    @7
    @4
    @3
    @1
    wo
    @3
    @0
    wo
    @0
    @1
    @3
    ax-a2
    @1
    @0
    @3
    @1
    wva
    wva
    wa
    #
    wvb
    wa
    #
    @0
    @12
    @1
    wva
    wva
    wvb
    anass
    ax-r1
    @11
    wva
    wvb
    wva
    anidm
    ran
    ax-r2
    lor
    @3
    @0
    @2
    @0
    lear
    df-le2
    3tr
    ax-r5
    @9
    @10
    @0
    @10
    @7
    @0
    @2
    leo
    @7
    @5
    @10
    @5
    @6
    lea
    @2
    @0
    ax-a2
    lbtr
    lel2or
    @2
    @7
    @0
    @2
    @5
    @6
    @2
    @0
    leo
    @0
    wva
    wva
    wvb
    lea
    lecon
    ler2an
    lelor
    lebi
    @0
    @2
    ax-a2
    3tr
    wva
    @0
    df-i4
    wva
    wvb
    df-i1
    3tr1
end
