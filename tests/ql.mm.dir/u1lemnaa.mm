include "wi1.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "anor2.mm"
include "u1lemona.mm"
include "ax-r4.mm"
include "df-a.mm"
include "lor.mm"
include "ax-r1.mm"
include "ax-r2.mm"

theorem u1lemnaa
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->1 b ) ' ^ a ) = ( a ^ ( a ' v b ' ) )

  proof
    wva
    wvb
    wi1
    #
    wn
    wva
    wa
    @0
    wva
    wn
    #
    wo
    #
    wn
    #
    wva
    @1
    wvb
    wn
    wo
    #
    wa
    #
    @0
    wva
    anor2
    @3
    @1
    wva
    wvb
    wa
    #
    wo
    #
    wn
    #
    @5
    @2
    @7
    wva
    wvb
    u1lemona
    ax-r4
    @5
    @8
    @5
    @1
    @4
    wn
    #
    wo
    #
    wn
    #
    @8
    wva
    @4
    df-a
    @8
    @11
    @7
    @10
    @6
    @9
    @1
    wva
    wvb
    df-a
    lor
    ax-r4
    ax-r1
    ax-r2
    ax-r1
    ax-r2
    ax-r2
end
