include "wn.mm"
include "wi3.mm"
include "wa.mm"
include "wo.mm"
include "df2i3.mm"
include "ax-a1.mm"
include "2an.mm"
include "ax-r5.mm"
include "ran.mm"
include "lor.mm"
include "2or.mm"
include "ax-r1.mm"
include "ax-r2.mm"

theorem i3n2
  param wva: term a
  param wvb: term b


  assert |- ( a ' ->3 b ' ) = ( ( a ^ b ) v ( ( a v b ' ) ^ ( a ' v ( a ^ b ' ) ) ) )

  proof
    wva
    wn
    #
    wvb
    wn
    #
    wi3
    @0
    wn
    #
    @1
    wn
    #
    wa
    #
    @2
    @1
    wo
    #
    @0
    @2
    @1
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    wva
    wvb
    wa
    #
    wva
    @1
    wo
    #
    @0
    wva
    @1
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    @0
    @1
    df2i3
    @15
    @9
    @10
    @4
    @14
    @8
    wva
    @2
    wvb
    @3
    wva
    ax-a1
    #
    wvb
    ax-a1
    2an
    @11
    @5
    @13
    @7
    wva
    @2
    @1
    @16
    ax-r5
    @12
    @6
    @0
    wva
    @2
    @1
    @16
    ran
    lor
    2an
    2or
    ax-r1
    ax-r2
end
