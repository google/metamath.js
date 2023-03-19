include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi4.mm"
include "df-i4.mm"
include "wf.mm"
include "ancom.mm"
include "anabs.mm"
include "ax-r2.mm"
include "oran.mm"
include "con2.mm"
include "ran.mm"
include "anass.mm"
include "ax-r1.mm"
include "dff.mm"
include "lan.mm"
include "an0.mm"
include "2or.mm"
include "or0.mm"
include "con3.mm"
include "lor.mm"
include "anor2.mm"
include "ax-r5.mm"
include "comid.mm"
include "comcom2.mm"
include "comorr.mm"
include "fh3r.mm"
include "wt.mm"
include "or32.mm"
include "oridm.mm"
include "df-t.mm"
include "ax-a2.mm"
include "2an.mm"
include "an1.mm"
include "oml.mm"

theorem ud4lem2
  let wva: term a
  let wvb: term b


  assert |- ( ( a v ( a ' ^ b ' ) ) ->4 a ) = ( a v b )

  proof
    wva
    wva
    wn
    #
    wvb
    wn
    wa
    #
    wo
    #
    wva
    wi4
    @2
    wva
    wa
    #
    @2
    wn
    #
    wva
    wa
    #
    wo
    #
    @4
    wva
    wo
    #
    @0
    wa
    #
    wo
    #
    wva
    wvb
    wo
    #
    @2
    wva
    df-i4
    @9
    wva
    @0
    @10
    wa
    #
    wo
    @10
    @6
    wva
    @8
    @11
    @6
    wva
    wf
    wo
    wva
    @3
    wva
    @5
    wf
    @3
    wva
    @2
    wa
    wva
    @2
    wva
    ancom
    wva
    @1
    anabs
    ax-r2
    @5
    @0
    @1
    wn
    #
    wa
    #
    wva
    wa
    #
    wf
    @4
    @13
    wva
    @2
    @13
    wva
    @1
    oran
    con2
    ran
    @14
    wva
    @13
    wa
    #
    wf
    @13
    wva
    ancom
    @15
    wva
    @0
    wa
    #
    @12
    wa
    #
    wf
    @17
    @15
    wva
    @0
    @12
    anass
    ax-r1
    @17
    @12
    @16
    wa
    #
    wf
    @16
    @12
    ancom
    @18
    @12
    wf
    wa
    #
    wf
    @19
    @18
    wf
    @16
    @12
    wva
    dff
    lan
    ax-r1
    @12
    an0
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    2or
    wva
    or0
    ax-r2
    @8
    @0
    @7
    wa
    @11
    @7
    @0
    ancom
    @7
    @10
    @0
    @7
    @11
    wva
    wo
    #
    @10
    @4
    @11
    wva
    @2
    @11
    @2
    wva
    @10
    wn
    #
    wo
    #
    @11
    wn
    @1
    @21
    wva
    @1
    @10
    @10
    @12
    wva
    wvb
    oran
    ax-r1
    con3
    lor
    @22
    @11
    @11
    @22
    wn
    wva
    @10
    anor2
    ax-r1
    con3
    ax-r2
    con2
    ax-r5
    @20
    @0
    wva
    wo
    #
    @10
    wva
    wo
    #
    wa
    #
    @10
    wva
    @0
    @10
    wva
    wva
    wva
    comid
    comcom2
    wva
    wvb
    comorr
    fh3r
    @25
    @10
    wt
    wa
    #
    @10
    @25
    @24
    @23
    wa
    @26
    @23
    @24
    ancom
    @24
    @10
    @23
    wt
    @24
    wva
    wva
    wo
    #
    wvb
    wo
    @10
    wva
    wvb
    wva
    or32
    @27
    wva
    wvb
    wva
    oridm
    ax-r5
    ax-r2
    wt
    @23
    wt
    wva
    @0
    wo
    @23
    wva
    df-t
    wva
    @0
    ax-a2
    ax-r2
    ax-r1
    2an
    ax-r2
    @10
    an1
    ax-r2
    ax-r2
    ax-r2
    lan
    ax-r2
    2or
    wva
    wvb
    oml
    ax-r2
    ax-r2
end
