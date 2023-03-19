include "wi5.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "ud5lem0c.mm"
include "ran.mm"
include "comorr.mm"
include "comcom6.mm"
include "com2an.mm"
include "comanr1.mm"
include "fh2.mm"
include "wf.mm"
include "anass.mm"
include "ancom.mm"
include "anabs.mm"
include "ax-r2.mm"
include "lan.mm"
include "an32.mm"
include "anor2.mm"
include "dff.mm"
include "ax-r1.mm"
include "an0.mm"
include "an0r.mm"
include "2or.mm"
include "or0.mm"

theorem ud5lem3b
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->5 b ) ' ^ ( a v ( a ' ^ b ) ) ) = ( a ^ ( a ' v b ' ) )

  proof
    wva
    wvb
    wi5
    wn
    #
    wva
    wva
    wn
    #
    wvb
    wa
    #
    wo
    #
    wa
    @1
    wvb
    wn
    #
    wo
    #
    wva
    @4
    wo
    #
    wa
    #
    wva
    wvb
    wo
    #
    wa
    #
    @3
    wa
    #
    wva
    @5
    wa
    #
    @0
    @9
    @3
    wva
    wvb
    ud5lem0c
    ran
    @10
    @9
    wva
    wa
    #
    @9
    @2
    wa
    #
    wo
    #
    @11
    wva
    @9
    @2
    wva
    @7
    @8
    wva
    @5
    @6
    wva
    @5
    @1
    @4
    comorr
    comcom6
    wva
    @4
    comorr
    com2an
    wva
    wvb
    comorr
    com2an
    wva
    @2
    @1
    wvb
    comanr1
    comcom6
    fh2
    @14
    @11
    wf
    wo
    @11
    @12
    @11
    @13
    wf
    @12
    @7
    @8
    wva
    wa
    #
    wa
    #
    @11
    @7
    @8
    wva
    anass
    @16
    @7
    wva
    wa
    #
    @11
    @15
    wva
    @7
    @15
    wva
    @8
    wa
    wva
    @8
    wva
    ancom
    wva
    wvb
    anabs
    ax-r2
    lan
    @17
    @5
    @6
    wva
    wa
    #
    wa
    #
    @11
    @5
    @6
    wva
    anass
    @19
    @5
    wva
    wa
    @11
    @18
    wva
    @5
    @18
    wva
    @6
    wa
    wva
    @6
    wva
    ancom
    wva
    @4
    anabs
    ax-r2
    lan
    @5
    wva
    ancom
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    @13
    @7
    @2
    wa
    #
    @8
    wa
    #
    wf
    @7
    @8
    @2
    an32
    @21
    wf
    @8
    wa
    wf
    @20
    wf
    @8
    @20
    @5
    @6
    @2
    wa
    #
    wa
    #
    wf
    @5
    @6
    @2
    anass
    @23
    @5
    wf
    wa
    wf
    @22
    wf
    @5
    @22
    @6
    @6
    wn
    #
    wa
    #
    wf
    @2
    @24
    @6
    wva
    wvb
    anor2
    lan
    wf
    @25
    @6
    dff
    ax-r1
    ax-r2
    lan
    @5
    an0
    ax-r2
    ax-r2
    ran
    @8
    an0r
    ax-r2
    ax-r2
    2or
    @11
    or0
    ax-r2
    ax-r2
    ax-r2
end
