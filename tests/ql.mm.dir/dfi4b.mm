include "wi4.mm"
include "wn.mm"
include "wi3.mm"
include "wo.mm"
include "wa.mm"
include "i4i3.mm"
include "dfi3b.mm"
include "ax-a2.mm"
include "ax-a1.mm"
include "ax-r5.mm"
include "ax-r2.mm"
include "ran.mm"
include "lor.mm"
include "2an.mm"
include "2or.mm"
include "or32.mm"
include "ax-r1.mm"

theorem dfi4b
  let wva: term a
  let wvb: term b


  assert |- ( a ->4 b ) = ( ( a ' v b ) ^ ( ( b ' v ( b ^ a ' ) ) v ( b ^ a ) ) )

  proof
    wva
    wvb
    wi4
    wvb
    wn
    #
    wva
    wn
    #
    wi3
    #
    @1
    wvb
    wo
    #
    @0
    wvb
    @1
    wa
    #
    wo
    #
    wvb
    wva
    wa
    #
    wo
    #
    wa
    #
    wva
    wvb
    i4i3
    @2
    @0
    wn
    #
    @1
    wo
    #
    @0
    @9
    @1
    wn
    #
    wa
    #
    wo
    @9
    @1
    wa
    #
    wo
    #
    wa
    #
    @8
    @0
    @1
    dfi3b
    @8
    @15
    @3
    @10
    @7
    @14
    @3
    wvb
    @1
    wo
    @10
    @1
    wvb
    ax-a2
    wvb
    @9
    @1
    wvb
    ax-a1
    #
    ax-r5
    ax-r2
    @7
    @0
    @13
    wo
    #
    @12
    wo
    @14
    @5
    @17
    @6
    @12
    @4
    @13
    @0
    wvb
    @9
    @1
    @16
    ran
    lor
    wvb
    @9
    wva
    @11
    @16
    wva
    ax-a1
    2an
    2or
    @0
    @13
    @12
    or32
    ax-r2
    2an
    ax-r1
    ax-r2
    ax-r2
end
