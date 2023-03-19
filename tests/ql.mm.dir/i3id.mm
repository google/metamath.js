include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi3.mm"
include "wt.mm"
include "wf.mm"
include "ancom.mm"
include "dff.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "anidm.mm"
include "2or.mm"
include "ax-a2.mm"
include "or0.mm"
include "df-t.mm"
include "lan.mm"
include "an1.mm"
include "df-i3.mm"
include "3tr1.mm"

theorem i3id
  param wva: term a


  assert |- ( a ->3 a ) = 1

  proof
    wva
    wn
    #
    wva
    wa
    #
    @0
    @0
    wa
    #
    wo
    #
    wva
    @0
    wva
    wo
    #
    wa
    #
    wo
    #
    wva
    @0
    wo
    #
    wva
    wva
    wi3
    wt
    @6
    @4
    @7
    @3
    @0
    @5
    wva
    @3
    @0
    wf
    wo
    #
    @0
    @3
    wf
    @0
    wo
    @8
    @1
    wf
    @2
    @0
    @1
    wva
    @0
    wa
    #
    wf
    @0
    wva
    ancom
    wf
    @9
    wva
    dff
    ax-r1
    ax-r2
    @0
    anidm
    2or
    wf
    @0
    ax-a2
    ax-r2
    @0
    or0
    ax-r2
    @5
    wva
    wt
    wa
    wva
    @4
    wt
    wva
    @4
    @7
    wt
    @0
    wva
    ax-a2
    #
    wt
    @7
    wva
    df-t
    #
    ax-r1
    ax-r2
    lan
    wva
    an1
    ax-r2
    2or
    @10
    ax-r2
    wva
    wva
    df-i3
    @11
    3tr1
end
