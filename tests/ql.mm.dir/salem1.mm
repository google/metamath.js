include "wn.mm"
include "wi1.mm"
include "wo.mm"
include "wa.mm"
include "wi2.mm"
include "u1lemob.mm"
include "ax-r4.mm"
include "anor1.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "ran.mm"
include "ax-a2.mm"
include "ancom.mm"
include "anabs.mm"
include "3tr.mm"
include "2or.mm"
include "df-i1.mm"
include "df-i2.mm"
include "3tr1.mm"

theorem salem1
  let wva: term a
  let wvb: term b


  assert |- ( ( ( a ' ->1 b ) v b ) ->1 b ) = ( a ->2 b )

  proof
    wva
    wn
    #
    wvb
    wi1
    wvb
    wo
    #
    wn
    #
    @1
    wvb
    wa
    #
    wo
    #
    wvb
    @0
    wvb
    wn
    wa
    #
    wo
    #
    @1
    wvb
    wi1
    wva
    wvb
    wi2
    @4
    @5
    wvb
    wo
    @6
    @2
    @5
    @3
    wvb
    @2
    @0
    wn
    #
    wvb
    wo
    #
    wn
    #
    @5
    @1
    @8
    @0
    wvb
    u1lemob
    #
    ax-r4
    @5
    @9
    @0
    wvb
    anor1
    ax-r1
    ax-r2
    @3
    @8
    wvb
    wa
    #
    wvb
    wvb
    @7
    wo
    #
    wa
    #
    wvb
    @1
    @8
    wvb
    @10
    ran
    @11
    @12
    wvb
    wa
    @13
    @8
    @12
    wvb
    @7
    wvb
    ax-a2
    ran
    @12
    wvb
    ancom
    ax-r2
    wvb
    @7
    anabs
    3tr
    2or
    @5
    wvb
    ax-a2
    ax-r2
    @1
    wvb
    df-i1
    wva
    wvb
    df-i2
    3tr1
end
