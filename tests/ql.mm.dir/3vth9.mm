include "wo.mm"
include "wn.mm"
include "wi2.mm"
include "wa.mm"
include "wi1.mm"
include "anor3.mm"
include "ax-r1.mm"
include "df-i2.mm"
include "lan.mm"
include "2or.mm"
include "df-i1.mm"
include "ud2lem0c.mm"
include "2an.mm"
include "anandi.mm"
include "anass.mm"
include "ax-r2.mm"
include "or32.mm"
include "comanr1.mm"
include "comcom6.mm"
include "comorr2.mm"
include "fh3.mm"
include "ancom.mm"
include "lor.mm"
include "or12.mm"
include "oridm.mm"
include "ax-r5.mm"
include "ax-a2.mm"
include "3tr1.mm"

theorem 3vth9
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a v b ) ->1 ( c ->2 b ) ) = ( ( b v c ) ->2 ( a ->2 b ) )

  proof
    wva
    wvb
    wo
    #
    wn
    #
    @0
    wvc
    wvb
    wi2
    #
    wa
    #
    wo
    wva
    wn
    wvb
    wn
    #
    wa
    #
    @0
    wvb
    wvc
    wn
    #
    @4
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    @0
    @2
    wi1
    wvb
    wvc
    wo
    #
    wva
    wvb
    wi2
    #
    wi2
    #
    @1
    @5
    @3
    @9
    @5
    @1
    wva
    wvb
    anor3
    ax-r1
    @2
    @8
    @0
    wvc
    wvb
    df-i2
    lan
    2or
    @0
    @2
    df-i1
    @13
    wvb
    @5
    wo
    #
    @4
    @6
    wa
    #
    @0
    wa
    #
    wo
    #
    @10
    @13
    @12
    @11
    wn
    #
    @12
    wn
    #
    wa
    #
    wo
    @17
    @11
    @12
    df-i2
    @12
    @14
    @20
    @16
    wva
    wvb
    df-i2
    @20
    @15
    @4
    @0
    wa
    #
    wa
    #
    @16
    @18
    @15
    @19
    @21
    @15
    @18
    wvb
    wvc
    anor3
    ax-r1
    wva
    wvb
    ud2lem0c
    2an
    @22
    @4
    @6
    @0
    wa
    wa
    #
    @16
    @23
    @22
    @4
    @6
    @0
    anandi
    ax-r1
    @16
    @23
    @4
    @6
    @0
    anass
    ax-r1
    ax-r2
    ax-r2
    2or
    ax-r2
    @17
    wvb
    @16
    wo
    #
    @5
    wo
    #
    @10
    wvb
    @5
    @16
    or32
    @25
    @9
    @5
    wo
    @10
    @24
    @9
    @5
    @24
    wvb
    @15
    wo
    #
    wvb
    @0
    wo
    #
    wa
    #
    @9
    wvb
    @15
    @0
    wvb
    @15
    @4
    @6
    comanr1
    comcom6
    wva
    wvb
    comorr2
    fh3
    @28
    @8
    @0
    wa
    @9
    @26
    @8
    @27
    @0
    @15
    @7
    wvb
    @4
    @6
    ancom
    lor
    @27
    wva
    wvb
    wvb
    wo
    #
    wo
    @0
    wvb
    wva
    wvb
    or12
    @29
    wvb
    wva
    wvb
    oridm
    lor
    ax-r2
    2an
    @8
    @0
    ancom
    ax-r2
    ax-r2
    ax-r5
    @9
    @5
    ax-a2
    ax-r2
    ax-r2
    ax-r2
    3tr1
end
