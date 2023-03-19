include "wi4.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "ud4lem1c.mm"
include "ud4lem0c.mm"
include "2an.mm"
include "an12.mm"
include "ax-a2.mm"
include "comor2.mm"
include "comcom3.mm"
include "comcom5.mm"
include "comor1.mm"
include "comcom2.mm"
include "com2an.mm"
include "fh1.mm"
include "wf.mm"
include "anor1.mm"
include "dff.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "ancom.mm"
include "anabs.mm"
include "2or.mm"
include "or0.mm"

theorem ud4lem1d
  let wva: term a
  let wvb: term b


  assert |- ( ( ( a ->4 b ) ' v ( b ->4 a ) ) ^ ( b ->4 a ) ' ) = ( ( ( a ' v b ' ) ^ ( a ' v b ) ) ^ a )

  proof
    wva
    wvb
    wi4
    wn
    wvb
    wva
    wi4
    #
    wo
    #
    @0
    wn
    #
    wa
    wva
    wvb
    wn
    #
    wo
    #
    @3
    wva
    wn
    #
    wo
    #
    wvb
    @5
    wo
    #
    wa
    #
    wvb
    @5
    wa
    #
    wva
    wo
    #
    wa
    #
    wa
    #
    @5
    @3
    wo
    #
    @5
    wvb
    wo
    #
    wa
    #
    wva
    wa
    #
    @1
    @4
    @2
    @11
    wva
    wvb
    ud4lem1c
    wvb
    wva
    ud4lem0c
    2an
    @12
    @8
    @4
    @10
    wa
    #
    wa
    @16
    @4
    @8
    @10
    an12
    @8
    @15
    @17
    wva
    @6
    @13
    @7
    @14
    @3
    @5
    ax-a2
    wvb
    @5
    ax-a2
    2an
    @17
    @4
    @9
    wa
    #
    @4
    wva
    wa
    #
    wo
    #
    wva
    @4
    @9
    wva
    @4
    wvb
    @5
    @4
    wvb
    @4
    @3
    wva
    @3
    comor2
    comcom3
    comcom5
    @4
    wva
    wva
    @3
    comor1
    #
    comcom2
    com2an
    @21
    fh1
    @20
    wf
    wva
    wo
    #
    wva
    @18
    wf
    @19
    wva
    @18
    @3
    wva
    wo
    #
    @23
    wn
    #
    wa
    #
    wf
    @4
    @23
    @9
    @24
    wva
    @3
    ax-a2
    wvb
    wva
    anor1
    2an
    wf
    @25
    @23
    dff
    ax-r1
    ax-r2
    @19
    wva
    @4
    wa
    wva
    @4
    wva
    ancom
    wva
    @3
    anabs
    ax-r2
    2or
    @22
    wva
    wf
    wo
    wva
    wf
    wva
    ax-a2
    wva
    or0
    ax-r2
    ax-r2
    ax-r2
    2an
    ax-r2
    ax-r2
end
