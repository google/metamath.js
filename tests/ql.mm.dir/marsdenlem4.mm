include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wf.mm"
include "leao3.mm"
include "oran1.mm"
include "lbtr.mm"
include "lecom.mm"
include "comcom7.mm"
include "leao4.mm"
include "oran2.mm"
include "fh1r.mm"
include "ancom.mm"
include "lan.mm"
include "an4.mm"
include "dff.mm"
include "ax-r1.mm"
include "an0.mm"
include "ax-r2.mm"
include "3tr.mm"
include "2or.mm"
include "or0.mm"

theorem marsdenlem4
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume marsden.1: |- a C b
  assume marsden.2: |- b C c
  assume marsden.3: |- c C d
  assume marsden.4: |- d C a


  assert |- ( ( ( a ' ^ b ) v ( a ^ d ' ) ) ^ ( b ' ^ d ) ) = 0

  proof
    wva
    wn
    #
    wvb
    wa
    #
    wva
    wvd
    wn
    #
    wa
    #
    wo
    wvb
    wn
    #
    wvd
    wa
    #
    wa
    @1
    @5
    wa
    #
    @3
    @5
    wa
    #
    wo
    wf
    wf
    wo
    wf
    @5
    @1
    @3
    @5
    @1
    @5
    @1
    wn
    #
    @5
    wva
    @4
    wo
    @8
    @4
    wvd
    wva
    leao3
    wva
    wvb
    oran1
    lbtr
    lecom
    comcom7
    @5
    @3
    @5
    @3
    wn
    #
    @5
    @0
    wvd
    wo
    @9
    wvd
    @4
    @0
    leao4
    wva
    wvd
    oran2
    lbtr
    lecom
    comcom7
    fh1r
    @6
    wf
    @7
    wf
    @6
    @1
    wvd
    @4
    wa
    #
    wa
    @0
    wvd
    wa
    #
    wvb
    @4
    wa
    #
    wa
    #
    wf
    @5
    @10
    @1
    @4
    wvd
    ancom
    lan
    @0
    wvb
    wvd
    @4
    an4
    @13
    @11
    wf
    wa
    #
    wf
    @14
    @13
    wf
    @12
    @11
    wvb
    dff
    lan
    ax-r1
    @11
    an0
    ax-r2
    3tr
    @7
    wva
    @4
    wa
    #
    @2
    wvd
    wa
    #
    wa
    @15
    wf
    wa
    wf
    wva
    @2
    @4
    wvd
    an4
    @16
    wf
    @15
    @16
    wvd
    @2
    wa
    #
    wf
    @2
    wvd
    ancom
    wf
    @17
    wvd
    dff
    ax-r1
    ax-r2
    lan
    @15
    an0
    3tr
    2or
    wf
    or0
    3tr
end
