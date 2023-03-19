include "wn.mm"
include "wo.mm"
include "wid4.mm"
include "wi1.mm"
include "wid3.mm"
include "wi2.mm"
include "wa.mm"
include "ancom.mm"
include "anor3.mm"
include "ax-r2.mm"
include "ax-r1.mm"
include "lor.mm"
include "ax-r4.mm"
include "lan.mm"
include "2or.mm"
include "2an.mm"
include "df-id4.mm"
include "3tr1.mm"
include "nom24.mm"
include "nomcon3.mm"
include "i2i1.mm"

theorem nom53
  param wva: term a
  param wvb: term b


  assert |- ( ( a v b ) ==3 b ) = ( a ->2 b )

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
    wid4
    #
    @0
    wva
    wn
    #
    wi1
    #
    @1
    wvb
    wid3
    wva
    wvb
    wi2
    @3
    @0
    @0
    @4
    wa
    #
    wid4
    #
    @5
    @0
    wn
    #
    @2
    wo
    #
    @2
    wn
    #
    @0
    @2
    wa
    #
    wo
    #
    wa
    @8
    @6
    wo
    #
    @6
    wn
    #
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
    @13
    @12
    @16
    @2
    @6
    @8
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
    lor
    @10
    @14
    @11
    @15
    @2
    @6
    @17
    ax-r4
    @2
    @6
    @0
    @17
    lan
    2or
    2an
    @0
    @2
    df-id4
    @0
    @6
    df-id4
    3tr1
    @0
    @4
    nom24
    ax-r2
    @1
    wvb
    nomcon3
    wva
    wvb
    i2i1
    3tr1
end
