include "wn.mm"
include "wo.mm"
include "wa.mm"
include "ax-a2.mm"
include "ax-a3.mm"
include "3tr1.mm"
include "ax-r2.mm"
include "ax-r1.mm"
include "oridm.mm"
include "ax-r5.mm"
include "ancom.mm"
include "2or.mm"
include "orabs.mm"
include "3tr2.mm"

theorem omlem1
  param wva: term a
  param wvb: term b


  assert |- ( ( a v ( a ' ^ ( a v b ) ) ) v ( a v b ) ) = ( a v b )

  proof
    wva
    wva
    wn
    #
    wva
    wvb
    wo
    #
    wa
    #
    wo
    #
    wva
    wo
    wvb
    wo
    #
    @1
    wva
    wo
    #
    @2
    wo
    #
    @3
    @1
    wo
    #
    @1
    @7
    @1
    @3
    wo
    @4
    @6
    @3
    @1
    ax-a2
    @3
    wva
    wvb
    ax-a3
    #
    @1
    wva
    @2
    ax-a3
    3tr1
    @8
    @6
    @1
    @1
    @0
    wa
    #
    wo
    @1
    @5
    @1
    @2
    @9
    @5
    wva
    wva
    wo
    #
    wvb
    wo
    #
    @1
    @11
    @5
    @11
    wva
    @1
    wo
    @5
    wva
    wva
    wvb
    ax-a3
    wva
    @1
    ax-a2
    ax-r2
    ax-r1
    @10
    wva
    wvb
    wva
    oridm
    ax-r5
    ax-r2
    @0
    @1
    ancom
    2or
    @1
    @0
    orabs
    ax-r2
    3tr2
end
