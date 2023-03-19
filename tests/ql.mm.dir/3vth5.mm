include "wo.mm"
include "wn.mm"
include "wa.mm"
include "wi2.mm"
include "ax-a3.mm"
include "or12.mm"
include "comorr.mm"
include "comcom2.mm"
include "fh3.mm"
include "ax-r1.mm"
include "oridm.mm"
include "ax-r5.mm"
include "ax-r2.mm"
include "ancom.mm"
include "anor3.mm"
include "lor.mm"
include "2an.mm"
include "df-i2.mm"
include "ax-a1.mm"
include "ran.mm"
include "3tr1.mm"

theorem 3vth5
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( a ->2 b ) ' ->2 ( b v c ) ) = ( c v ( ( a ->2 b ) ^ ( c ->2 b ) ) )

  proof
    wvb
    wvc
    wo
    #
    wvb
    wva
    wn
    wvb
    wn
    #
    wa
    #
    wo
    #
    @0
    wn
    #
    wa
    #
    wo
    #
    wvc
    @3
    wvb
    wvc
    wn
    #
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
    wi2
    #
    wn
    #
    @0
    wi2
    #
    wvc
    @12
    wvc
    wvb
    wi2
    #
    wa
    #
    wo
    @6
    wvb
    wvc
    @5
    wo
    wo
    #
    @11
    wvb
    wvc
    @5
    ax-a3
    @17
    wvc
    wvb
    @5
    wo
    #
    wo
    @11
    wvb
    wvc
    @5
    or12
    @18
    @10
    wvc
    @18
    wvb
    @3
    wo
    #
    wvb
    @4
    wo
    #
    wa
    @10
    wvb
    @3
    @4
    wvb
    @2
    comorr
    wvb
    @0
    wvb
    wvc
    comorr
    comcom2
    fh3
    @19
    @3
    @20
    @9
    @19
    wvb
    wvb
    wo
    #
    @2
    wo
    #
    @3
    @22
    @19
    wvb
    wvb
    @2
    ax-a3
    ax-r1
    @21
    wvb
    @2
    wvb
    oridm
    ax-r5
    ax-r2
    @4
    @8
    wvb
    @8
    @4
    @8
    @1
    @7
    wa
    @4
    @7
    @1
    ancom
    wvb
    wvc
    anor3
    ax-r2
    ax-r1
    lor
    2an
    ax-r2
    lor
    ax-r2
    ax-r2
    @14
    @0
    @13
    wn
    #
    @4
    wa
    #
    wo
    #
    @6
    @13
    @0
    df-i2
    @6
    @25
    @5
    @24
    @0
    @3
    @23
    @4
    @3
    @12
    @23
    @12
    @3
    wva
    wvb
    df-i2
    #
    ax-r1
    @12
    ax-a1
    ax-r2
    ran
    lor
    ax-r1
    ax-r2
    @16
    @10
    wvc
    @12
    @3
    @15
    @9
    @26
    wvc
    wvb
    df-i2
    2an
    lor
    3tr1
end
