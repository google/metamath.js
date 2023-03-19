include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wf.mm"
include "lea.mm"
include "lecon.mm"
include "lel.mm"
include "lecom.mm"
include "comcom7.mm"
include "comcom.mm"
include "lear.mm"
include "lerr.mm"
include "oran2.mm"
include "lbtr.mm"
include "fh1r.mm"
include "an4.mm"
include "ancom.mm"
include "dff.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "ran.mm"
include "an0r.mm"
include "3tr.mm"
include "lan.mm"
include "an0.mm"
include "2or.mm"
include "or0.mm"

theorem marsdenlem3
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume marsden.1: |- a C b
  assume marsden.2: |- b C c
  assume marsden.3: |- c C d
  assume marsden.4: |- d C a


  assert |- ( ( ( b ' ^ c ) v ( c ' ^ d ) ) ^ ( b ^ d ' ) ) = 0

  proof
    wvb
    wn
    #
    wvc
    wa
    #
    wvc
    wn
    #
    wvd
    wa
    #
    wo
    wvb
    wvd
    wn
    #
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
    @1
    @5
    @1
    @5
    @1
    @5
    wn
    #
    @0
    @8
    wvc
    @5
    wvb
    wvb
    @4
    lea
    lecon
    lel
    lecom
    comcom7
    comcom
    @3
    @5
    @3
    @5
    @3
    @8
    @3
    @0
    wvd
    wo
    @8
    @3
    wvd
    @0
    @2
    wvd
    lear
    lerr
    wvb
    wvd
    oran2
    lbtr
    lecom
    comcom7
    comcom
    fh1r
    @6
    wf
    @7
    wf
    @6
    @0
    wvb
    wa
    #
    wvc
    @4
    wa
    #
    wa
    wf
    @10
    wa
    wf
    @0
    wvc
    wvb
    @4
    an4
    @9
    wf
    @10
    @9
    wvb
    @0
    wa
    #
    wf
    @0
    wvb
    ancom
    wf
    @11
    wvb
    dff
    ax-r1
    ax-r2
    ran
    @10
    an0r
    3tr
    @7
    @2
    wvb
    wa
    #
    wvd
    @4
    wa
    #
    wa
    @12
    wf
    wa
    wf
    @2
    wvd
    wvb
    @4
    an4
    @13
    wf
    @12
    wf
    @13
    wvd
    dff
    ax-r1
    lan
    @12
    an0
    3tr
    2or
    wf
    or0
    3tr
end
