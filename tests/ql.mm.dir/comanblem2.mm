include "wa.mm"
include "tb.mm"
include "wn.mm"
include "wo.mm"
include "dfb.mm"
include "2an.mm"
include "lan.mm"
include "wf.mm"
include "comanr1.mm"
include "comcom6.mm"
include "fh1.mm"
include "anass.mm"
include "ax-r1.mm"
include "anidm.mm"
include "ran.mm"
include "ax-r2.mm"
include "dff.mm"
include "an0r.mm"
include "3tr2.mm"
include "2or.mm"
include "or0.mm"
include "3tr.mm"
include "an4.mm"
include "anandir.mm"
include "3tr1.mm"

theorem comanblem2
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a ^ b ) ^ ( ( a == c ) ^ ( b == c ) ) ) = ( ( a ^ b ) ^ c )

  proof
    wva
    wvb
    wa
    #
    wva
    wvc
    tb
    #
    wvb
    wvc
    tb
    #
    wa
    #
    wa
    @0
    wva
    wvc
    wa
    #
    wva
    wn
    #
    wvc
    wn
    #
    wa
    #
    wo
    #
    wvb
    wvc
    wa
    #
    wvb
    wn
    #
    @6
    wa
    #
    wo
    #
    wa
    #
    wa
    #
    @0
    wvc
    wa
    #
    @3
    @13
    @0
    @1
    @8
    @2
    @12
    wva
    wvc
    dfb
    wvb
    wvc
    dfb
    2an
    lan
    wva
    @8
    wa
    #
    wvb
    @12
    wa
    #
    wa
    @4
    @9
    wa
    @14
    @15
    @16
    @4
    @17
    @9
    @16
    wva
    @4
    wa
    #
    wva
    @7
    wa
    #
    wo
    @4
    wf
    wo
    @4
    wva
    @4
    @7
    wva
    wvc
    comanr1
    wva
    @7
    @5
    @6
    comanr1
    comcom6
    fh1
    @18
    @4
    @19
    wf
    @18
    wva
    wva
    wa
    #
    wvc
    wa
    #
    @4
    @21
    @18
    wva
    wva
    wvc
    anass
    ax-r1
    @20
    wva
    wvc
    wva
    anidm
    ran
    ax-r2
    wva
    @5
    wa
    #
    @6
    wa
    #
    wf
    @6
    wa
    #
    @19
    wf
    @24
    @23
    wf
    @22
    @6
    wva
    dff
    ran
    ax-r1
    wva
    @5
    @6
    anass
    @6
    an0r
    #
    3tr2
    2or
    @4
    or0
    3tr
    @17
    wvb
    @9
    wa
    #
    wvb
    @11
    wa
    #
    wo
    @9
    wf
    wo
    @9
    wvb
    @9
    @11
    wvb
    wvc
    comanr1
    wvb
    @11
    @10
    @6
    comanr1
    comcom6
    fh1
    @26
    @9
    @27
    wf
    @26
    wvb
    wvb
    wa
    #
    wvc
    wa
    #
    @9
    @29
    @26
    wvb
    wvb
    wvc
    anass
    ax-r1
    @28
    wvb
    wvc
    wvb
    anidm
    ran
    ax-r2
    wvb
    @10
    wa
    #
    @6
    wa
    #
    @24
    @27
    wf
    @24
    @31
    wf
    @30
    @6
    wvb
    dff
    ran
    ax-r1
    wvb
    @10
    @6
    anass
    @25
    3tr2
    2or
    @9
    or0
    3tr
    2an
    wva
    wvb
    @8
    @12
    an4
    wva
    wvb
    wvc
    anandir
    3tr1
    ax-r2
end
