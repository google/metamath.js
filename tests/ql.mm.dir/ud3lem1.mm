include "wi3.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "df-i3.mm"
include "wf.mm"
include "ud3lem1a.mm"
include "ud3lem1b.mm"
include "2or.mm"
include "or0.mm"
include "ax-r2.mm"
include "ud3lem1d.mm"
include "coman1.mm"
include "comcom2.mm"
include "coman2.mm"
include "comcom7.mm"
include "com2or.mm"
include "fh3.mm"
include "wt.mm"
include "ax-a2.mm"
include "orabs.mm"
include "anor1.mm"
include "lor.mm"
include "df-t.mm"
include "ax-r1.mm"
include "2an.mm"
include "an1.mm"
include "or12.mm"
include "3tr1.mm"

theorem ud3lem1
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->3 b ) ->3 ( b ->3 a ) ) = ( a v ( a ' ^ b ' ) )

  proof
    wva
    wvb
    wi3
    #
    wvb
    wva
    wi3
    #
    wi3
    @0
    wn
    #
    @1
    wa
    #
    @2
    @1
    wn
    wa
    #
    wo
    #
    @0
    @2
    @1
    wo
    wa
    #
    wo
    #
    wva
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
    @1
    df-i3
    @7
    wva
    @9
    wa
    #
    @10
    wva
    @8
    wvb
    wo
    #
    wa
    #
    wo
    #
    wo
    #
    @11
    @5
    @12
    @6
    @15
    @5
    @12
    wf
    wo
    @12
    @3
    @12
    @4
    wf
    wva
    wvb
    ud3lem1a
    wva
    wvb
    ud3lem1b
    2or
    @12
    or0
    ax-r2
    wva
    wvb
    ud3lem1d
    2or
    @10
    @12
    @14
    wo
    #
    wo
    @10
    wva
    wo
    @16
    @11
    @17
    wva
    @10
    @17
    @12
    wva
    wo
    #
    @12
    @13
    wo
    #
    wa
    #
    wva
    @12
    wva
    @13
    wva
    @9
    coman1
    #
    @12
    @8
    wvb
    @12
    wva
    @21
    comcom2
    @12
    wvb
    wva
    @9
    coman2
    comcom7
    com2or
    fh3
    @20
    wva
    wt
    wa
    wva
    @18
    wva
    @19
    wt
    @18
    wva
    @12
    wo
    wva
    @12
    wva
    ax-a2
    wva
    @9
    orabs
    ax-r2
    @19
    @13
    @12
    wo
    #
    wt
    @12
    @13
    ax-a2
    @22
    @13
    @13
    wn
    #
    wo
    #
    wt
    @12
    @23
    @13
    wva
    wvb
    anor1
    lor
    wt
    @24
    @13
    df-t
    ax-r1
    ax-r2
    ax-r2
    2an
    wva
    an1
    ax-r2
    ax-r2
    lor
    @12
    @10
    @14
    or12
    wva
    @10
    ax-a2
    3tr1
    ax-r2
    ax-r2
end
