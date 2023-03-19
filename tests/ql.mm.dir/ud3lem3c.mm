include "wi3.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "ud3lem0c.mm"
include "an32.mm"
include "ancom.mm"
include "ax-r2.mm"
include "ax-r5.mm"
include "ax-a2.mm"
include "orabs.mm"

theorem ud3lem3c
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->3 b ) ' v ( a v b ) ) = ( a v b )

  proof
    wva
    wvb
    wi3
    wn
    #
    wva
    wvb
    wo
    #
    wo
    @1
    wva
    wvb
    wn
    #
    wo
    #
    wva
    wn
    wva
    @2
    wa
    wo
    #
    wa
    #
    wa
    #
    @1
    wo
    #
    @1
    @0
    @6
    @1
    @0
    @3
    @1
    wa
    @4
    wa
    #
    @6
    wva
    wvb
    ud3lem0c
    @8
    @5
    @1
    wa
    @6
    @3
    @1
    @4
    an32
    @5
    @1
    ancom
    ax-r2
    ax-r2
    ax-r5
    @7
    @1
    @6
    wo
    @1
    @6
    @1
    ax-a2
    @1
    @5
    orabs
    ax-r2
    ax-r2
end
