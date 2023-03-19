include "wi4.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "df-i4.mm"
include "ax-r5.mm"
include "or32.mm"
include "ax-a3.mm"
include "lea.mm"
include "df-le2.mm"
include "lor.mm"
include "ax-r2.mm"
include "comor1.mm"
include "comcom7.mm"
include "comor2.mm"
include "com2an.mm"
include "com2or.mm"
include "comcom2.mm"
include "fh4.mm"
include "wt.mm"
include "lear.mm"
include "leor.mm"
include "letr.mm"
include "leo.mm"
include "lel2or.mm"
include "df-a.mm"
include "ax-r1.mm"
include "con3.mm"
include "df-t.mm"
include "2an.mm"
include "an1.mm"

theorem u4lemona
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->4 b ) v a ' ) = ( a ' v b )

  proof
    wva
    wvb
    wi4
    #
    wva
    wn
    #
    wo
    wva
    wvb
    wa
    #
    @1
    wvb
    wa
    #
    wo
    #
    @1
    wvb
    wo
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    @1
    wo
    #
    @5
    @0
    @8
    @1
    wva
    wvb
    df-i4
    ax-r5
    @9
    @4
    @1
    wo
    #
    @7
    wo
    #
    @5
    @4
    @7
    @1
    or32
    @11
    @2
    @1
    wo
    #
    @7
    wo
    #
    @5
    @10
    @12
    @7
    @10
    @2
    @3
    @1
    wo
    #
    wo
    @12
    @2
    @3
    @1
    ax-a3
    @14
    @1
    @2
    @3
    @1
    @1
    wvb
    lea
    df-le2
    lor
    ax-r2
    ax-r5
    @13
    @12
    @5
    wo
    #
    @12
    @6
    wo
    #
    wa
    #
    @5
    @5
    @12
    @6
    @5
    @2
    @1
    @5
    wva
    wvb
    @5
    wva
    @1
    wvb
    comor1
    #
    comcom7
    @1
    wvb
    comor2
    #
    com2an
    @18
    com2or
    @5
    wvb
    @19
    comcom2
    fh4
    @17
    @5
    wt
    wa
    @5
    @15
    @5
    @16
    wt
    @12
    @5
    @2
    @5
    @1
    @2
    wvb
    @5
    wva
    wvb
    lear
    wvb
    @1
    leor
    letr
    @1
    wvb
    leo
    lel2or
    df-le2
    @16
    @2
    @1
    @6
    wo
    #
    wo
    #
    wt
    @2
    @1
    @6
    ax-a3
    @21
    @2
    @2
    wn
    #
    wo
    #
    wt
    @20
    @22
    @2
    @20
    @2
    @2
    @20
    wn
    wva
    wvb
    df-a
    ax-r1
    con3
    lor
    wt
    @23
    @2
    df-t
    ax-r1
    ax-r2
    ax-r2
    2an
    @5
    an1
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
