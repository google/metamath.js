include "wi2.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "oridm.mm"
include "ax-r1.mm"
include "3vth4.mm"
include "lor.mm"
include "3vth5.mm"
include "ax-a2.mm"
include "ud2lem0a.mm"
include "ax-r2.mm"
include "2or.mm"
include "or4.mm"
include "ax-r5.mm"
include "leo.mm"
include "df-i2.mm"
include "lbtr.mm"
include "ler2an.mm"
include "df-le2.mm"

theorem 3vth6
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( a ->2 b ) ' ->2 ( b v c ) ) = ( ( ( a ->2 b ) ^ ( c ->2 b ) ) v ( ( a ->2 c ) ^ ( b ->2 c ) ) )

  proof
    wva
    wvb
    wi2
    #
    wn
    wvb
    wvc
    wo
    #
    wi2
    #
    @2
    @2
    wo
    #
    @0
    wvc
    wvb
    wi2
    #
    wa
    #
    wva
    wvc
    wi2
    #
    wvb
    wvc
    wi2
    #
    wa
    #
    wo
    #
    @3
    @2
    @2
    oridm
    ax-r1
    @3
    @2
    @6
    wn
    #
    @1
    wi2
    #
    wo
    #
    @9
    @2
    @11
    @2
    wva
    wvb
    wvc
    3vth4
    lor
    @12
    wvc
    @5
    wo
    #
    wvb
    @8
    wo
    #
    wo
    #
    @9
    @2
    @13
    @11
    @14
    wva
    wvb
    wvc
    3vth5
    @11
    @10
    wvc
    wvb
    wo
    #
    wi2
    @14
    @1
    @16
    @10
    wvb
    wvc
    ax-a2
    ud2lem0a
    wva
    wvc
    wvb
    3vth5
    ax-r2
    2or
    @15
    @16
    @9
    wo
    #
    @9
    wvc
    @5
    wvb
    @8
    or4
    @17
    @1
    @9
    wo
    #
    @9
    @16
    @1
    @9
    wvc
    wvb
    ax-a2
    ax-r5
    @18
    wvb
    @5
    wo
    #
    wvc
    @8
    wo
    #
    wo
    @9
    wvb
    wvc
    @5
    @8
    or4
    @19
    @5
    @20
    @8
    wvb
    @5
    wvb
    @0
    @4
    wvb
    wvb
    wva
    wn
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    @0
    wvb
    @23
    leo
    @0
    @24
    wva
    wvb
    df-i2
    ax-r1
    lbtr
    wvb
    wvb
    wvc
    wn
    #
    @22
    wa
    #
    wo
    #
    @4
    wvb
    @26
    leo
    @4
    @27
    wvc
    wvb
    df-i2
    ax-r1
    lbtr
    ler2an
    df-le2
    wvc
    @8
    wvc
    @6
    @7
    wvc
    wvc
    @21
    @25
    wa
    #
    wo
    #
    @6
    wvc
    @28
    leo
    @6
    @29
    wva
    wvc
    df-i2
    ax-r1
    lbtr
    wvc
    wvc
    @22
    @25
    wa
    #
    wo
    #
    @7
    wvc
    @30
    leo
    @7
    @31
    wvb
    wvc
    df-i2
    ax-r1
    lbtr
    ler2an
    df-le2
    2or
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
