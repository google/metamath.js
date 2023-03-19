include "wi2.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "oaliii.mm"
include "lan.mm"
include "anidm.mm"
include "ax-r1.mm"
include "anandir.mm"
include "3tr1.mm"
include "ax-a2.mm"
include "anabs.mm"
include "3tr.mm"

theorem oath1
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( a ->2 b ) ^ ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) = ( ( a ->2 b ) ^ ( a ->2 c ) )

  proof
    wva
    wvb
    wi2
    #
    wvb
    wvc
    wo
    wn
    #
    @0
    wva
    wvc
    wi2
    #
    wa
    #
    wo
    #
    wa
    #
    @3
    @4
    wa
    #
    @3
    @3
    @1
    wo
    #
    wa
    @3
    @5
    @5
    wa
    #
    @5
    @2
    @4
    wa
    #
    wa
    @5
    @6
    @5
    @9
    @5
    wva
    wvb
    wvc
    oaliii
    lan
    @8
    @5
    @5
    anidm
    ax-r1
    @0
    @2
    @4
    anandir
    3tr1
    @4
    @7
    @3
    @1
    @3
    ax-a2
    lan
    @3
    @1
    anabs
    3tr
end
