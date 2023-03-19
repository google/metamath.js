include "wi1.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "df-i1.mm"
include "ancom.mm"
include "2or.mm"
include "u1lemab.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "lor.mm"
include "id.mm"

theorem u1lem3
  let wva: term a
  let wvb: term b


  assert |- ( a ->1 ( b ->1 a ) ) = ( a ' v ( ( a ^ b ) v ( a ^ b ' ) ) )

  proof
    wva
    wvb
    wva
    wi1
    #
    wi1
    wva
    wn
    #
    wva
    @0
    wa
    #
    wo
    #
    @1
    wva
    wvb
    wa
    #
    wva
    wvb
    wn
    #
    wa
    #
    wo
    #
    wo
    #
    wva
    @0
    df-i1
    @3
    @8
    @8
    @2
    @7
    @1
    @7
    @2
    @7
    @0
    wva
    wa
    #
    @2
    @7
    wvb
    wva
    wa
    #
    @5
    wva
    wa
    #
    wo
    #
    @9
    @4
    @10
    @6
    @11
    wva
    wvb
    ancom
    wva
    @5
    ancom
    2or
    @9
    @12
    wvb
    wva
    u1lemab
    ax-r1
    ax-r2
    @0
    wva
    ancom
    ax-r2
    ax-r1
    lor
    @8
    id
    ax-r2
    ax-r2
end
