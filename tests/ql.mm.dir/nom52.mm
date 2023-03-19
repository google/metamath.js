include "wn.mm"
include "wo.mm"
include "wid1.mm"
include "wi1.mm"
include "wid2.mm"
include "wi2.mm"
include "wa.mm"
include "ancom.mm"
include "anor3.mm"
include "ax-r2.mm"
include "ax-r1.mm"
include "ax-r4.mm"
include "lor.mm"
include "lan.mm"
include "2an.mm"
include "df-id1.mm"
include "3tr1.mm"
include "nom21.mm"
include "nomcon2.mm"
include "i2i1.mm"

theorem nom52
  let wva: term a
  let wvb: term b


  assert |- ( ( a v b ) ==2 b ) = ( a ->2 b )

  proof
    wvb
    wn
    #
    wva
    wvb
    wo
    #
    wn
    #
    wid1
    #
    @0
    wva
    wn
    #
    wi1
    #
    @1
    wvb
    wid2
    wva
    wvb
    wi2
    @3
    @0
    @0
    @4
    wa
    #
    wid1
    #
    @5
    @0
    @2
    wn
    #
    wo
    #
    @0
    wn
    #
    @0
    @2
    wa
    #
    wo
    #
    wa
    @0
    @6
    wn
    #
    wo
    #
    @10
    @0
    @6
    wa
    #
    wo
    #
    wa
    @3
    @7
    @9
    @14
    @12
    @16
    @8
    @13
    @0
    @2
    @6
    @6
    @2
    @6
    @4
    @0
    wa
    @2
    @0
    @4
    ancom
    wva
    wvb
    anor3
    ax-r2
    ax-r1
    #
    ax-r4
    lor
    @11
    @15
    @10
    @2
    @6
    @0
    @17
    lan
    lor
    2an
    @0
    @2
    df-id1
    @0
    @6
    df-id1
    3tr1
    @0
    @4
    nom21
    ax-r2
    @1
    wvb
    nomcon2
    wva
    wvb
    i2i1
    3tr1
end
