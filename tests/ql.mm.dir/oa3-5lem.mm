include "wa.mm"
include "wi1.mm"
include "wt.mm"
include "wo.mm"
include "wn.mm"
include "or12.mm"
include "oridm.mm"
include "lor.mm"
include "ax-r2.mm"
include "an1.mm"
include "df-i1.mm"
include "3tr1.mm"
include "ancom.mm"
include "ax-r5.mm"
include "3tr.mm"
include "lan.mm"
include "2or.mm"

theorem oa3-5lem
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a ->1 c ) ^ ( a v ( c ^ ( ( ( a ^ c ) v ( ( a ->1 c ) ^ 1 ) ) v ( ( ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ^ ( ( c ^ b ) v ( 1 ^ ( b ->1 c ) ) ) ) ) ) ) ) = ( ( a ->1 c ) ^ ( a v ( c ^ ( ( a ->1 c ) v ( ( b ->1 c ) ^ ( ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) ) ) )

  proof
    wva
    wvc
    wva
    wvc
    wa
    #
    wva
    wvc
    wi1
    #
    wt
    wa
    #
    wo
    #
    wva
    wvb
    wa
    @1
    wvb
    wvc
    wi1
    #
    wa
    wo
    #
    wvc
    wvb
    wa
    #
    wt
    @4
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    wa
    #
    wo
    wva
    wvc
    @1
    @4
    @5
    wa
    #
    wo
    #
    wa
    #
    wo
    @1
    @11
    @14
    wva
    @10
    @13
    wvc
    @3
    @1
    @9
    @12
    @0
    wva
    wn
    #
    @0
    wo
    #
    wo
    #
    @16
    @3
    @1
    @17
    @15
    @0
    @0
    wo
    #
    wo
    @16
    @0
    @15
    @0
    or12
    @18
    @0
    @15
    @0
    oridm
    lor
    ax-r2
    @2
    @16
    @0
    @2
    @1
    @16
    @1
    an1
    wva
    wvc
    df-i1
    #
    ax-r2
    lor
    @19
    3tr1
    @9
    @5
    @4
    wa
    @12
    @8
    @4
    @5
    @6
    wvb
    wn
    #
    wvb
    wvc
    wa
    #
    wo
    #
    wo
    #
    @22
    @8
    @4
    @23
    @20
    @6
    @21
    wo
    #
    wo
    @22
    @6
    @20
    @21
    or12
    @24
    @21
    @20
    @24
    @21
    @21
    wo
    @21
    @6
    @21
    @21
    wvc
    wvb
    ancom
    ax-r5
    @21
    oridm
    ax-r2
    lor
    ax-r2
    @7
    @22
    @6
    @7
    @4
    wt
    wa
    @4
    @22
    wt
    @4
    ancom
    @4
    an1
    wvb
    wvc
    df-i1
    #
    3tr
    lor
    @25
    3tr1
    lan
    @5
    @4
    ancom
    ax-r2
    2or
    lan
    lor
    lan
end
