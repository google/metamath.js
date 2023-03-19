include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi4.mm"
include "oran1.mm"
include "df-a.mm"
include "anor1.mm"
include "2or.mm"
include "ax-r4.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "ancom.mm"
include "ran.mm"
include "anor2.mm"
include "anor3.mm"
include "2an.mm"
include "u4lem1.mm"
include "oran.mm"
include "3tr1.mm"

theorem u4lem1n
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->4 b ) ->4 a ) ' = ( ( ( ( a ' v b ) ^ ( a ' v b ' ) ) ^ a ) v ( ( a ' ^ b ) v ( a ' ^ b ' ) ) )

  proof
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
    wva
    wn
    #
    wo
    #
    wva
    wvb
    wo
    #
    wva
    @1
    wo
    #
    wa
    #
    wa
    #
    wn
    @4
    wvb
    wo
    #
    @4
    @1
    wo
    #
    wa
    #
    wva
    wa
    #
    wn
    #
    @4
    wvb
    wa
    #
    @4
    @1
    wa
    #
    wo
    #
    wn
    #
    wa
    #
    wn
    wva
    wvb
    wi4
    wva
    wi4
    #
    wn
    @13
    @17
    wo
    @9
    @19
    @5
    @14
    @8
    @18
    @5
    @3
    wn
    #
    wva
    wa
    #
    wn
    @14
    @3
    wva
    oran1
    @22
    @13
    @21
    @12
    wva
    @21
    @11
    @10
    wa
    #
    @12
    @21
    @11
    wn
    #
    @10
    wn
    #
    wo
    #
    wn
    #
    @23
    @3
    @26
    @0
    @24
    @2
    @25
    wva
    wvb
    df-a
    wva
    wvb
    anor1
    2or
    ax-r4
    @23
    @27
    @11
    @10
    df-a
    ax-r1
    ax-r2
    @11
    @10
    ancom
    ax-r2
    ran
    ax-r4
    ax-r2
    @8
    @7
    @6
    wa
    #
    @18
    @6
    @7
    ancom
    @28
    @7
    wn
    #
    @6
    wn
    #
    wo
    #
    wn
    #
    @18
    @7
    @6
    df-a
    @18
    @32
    @17
    @31
    @15
    @29
    @16
    @30
    wva
    wvb
    anor2
    wva
    wvb
    anor3
    2or
    ax-r4
    ax-r1
    ax-r2
    ax-r2
    2an
    ax-r4
    @20
    @9
    wva
    wvb
    u4lem1
    ax-r4
    @13
    @17
    oran
    3tr1
end
