include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi1.mm"
include "neg3antlem2.mm"
include "neg3antlem1.mm"
include "lel2or.mm"
include "df-i1.mm"
include "lbtr.mm"
include "wi3.mm"
include "ax-r1.mm"
include "lebi.mm"
include "3tr1.mm"

theorem neg3ant1
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume neg3ant.1: |- ( a ->3 c ) = ( b ->3 c )


  assert |- ( a ->1 c ) = ( b ->1 c )

  proof
    wva
    wn
    #
    wva
    wvc
    wa
    #
    wo
    #
    wvb
    wn
    #
    wvb
    wvc
    wa
    #
    wo
    #
    wva
    wvc
    wi1
    #
    wvb
    wvc
    wi1
    #
    @2
    @5
    @2
    @7
    @5
    @0
    @7
    @1
    wva
    wvb
    wvc
    neg3ant.1
    neg3antlem2
    wva
    wvb
    wvc
    neg3ant.1
    neg3antlem1
    lel2or
    wvb
    wvc
    df-i1
    #
    lbtr
    @5
    @6
    @2
    @3
    @6
    @4
    wvb
    wva
    wvc
    wva
    wvc
    wi3
    wvb
    wvc
    wi3
    neg3ant.1
    ax-r1
    #
    neg3antlem2
    wvb
    wva
    wvc
    @9
    neg3antlem1
    lel2or
    wva
    wvc
    df-i1
    #
    lbtr
    lebi
    @10
    @8
    3tr1
end
