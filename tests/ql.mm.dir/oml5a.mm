include "wo.mm"
include "wn.mm"
include "wa.mm"
include "omla.mm"
include "anass.mm"
include "ax-a2.mm"
include "lan.mm"
include "anabs.mm"
include "ax-r2.mm"
include "ran.mm"
include "an12.mm"
include "3tr2.mm"
include "lor.mm"
include "3tr1.mm"

theorem oml5a
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( a v b ) ^ ( ( a v b ) ' v ( b ^ c ) ) ) = ( b ^ c )

  proof
    wva
    wvb
    wo
    #
    @0
    wn
    #
    wvb
    wvc
    wa
    #
    wo
    #
    wa
    #
    wvb
    @0
    wa
    #
    wvc
    wa
    #
    @2
    @0
    @1
    @0
    @2
    wa
    #
    wo
    #
    wa
    @7
    @4
    @6
    @0
    @2
    omla
    @3
    @8
    @0
    @2
    @7
    @1
    @6
    wvb
    @0
    wvc
    wa
    wa
    #
    @2
    @7
    wvb
    @0
    wvc
    anass
    #
    @5
    wvb
    wvc
    @5
    wvb
    wvb
    wva
    wo
    #
    wa
    wvb
    @0
    @11
    wvb
    wva
    wvb
    ax-a2
    lan
    wvb
    wva
    anabs
    ax-r2
    ran
    #
    wvb
    @0
    wvc
    an12
    #
    3tr2
    lor
    lan
    @6
    @9
    @7
    @10
    @13
    ax-r2
    3tr1
    @12
    ax-r2
end
