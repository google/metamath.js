include "wn.mm"
include "wi3.mm"
include "wa.mm"
include "wo.mm"
include "df-i3.mm"
include "ax-a1.mm"
include "ran.mm"
include "2an.mm"
include "2or.mm"
include "ax-r5.mm"
include "lan.mm"
include "ax-r1.mm"
include "ax-r2.mm"

theorem i3n1
  let wva: term a
  let wvb: term b


  assert |- ( a ' ->3 b ' ) = ( ( ( a ^ b ' ) v ( a ^ b ) ) v ( a ' ^ ( a v b ' ) ) )

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
    wa
    #
    @2
    @1
    wn
    #
    wa
    #
    wo
    #
    @0
    @2
    @1
    wo
    #
    wa
    #
    wo
    #
    wva
    @1
    wa
    #
    wva
    wvb
    wa
    #
    wo
    #
    @0
    wva
    @1
    wo
    #
    wa
    #
    wo
    #
    @0
    @1
    df-i3
    @15
    @9
    @12
    @6
    @14
    @8
    @10
    @3
    @11
    @5
    wva
    @2
    @1
    wva
    ax-a1
    #
    ran
    wva
    @2
    wvb
    @4
    @16
    wvb
    ax-a1
    2an
    2or
    @13
    @7
    @0
    wva
    @2
    @1
    @16
    ax-r5
    lan
    2or
    ax-r1
    ax-r2
end
