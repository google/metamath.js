include "wn.mm"
include "wa.mm"
include "wf.mm"
include "an0.mm"
include "ax-r1.mm"
include "ancom.mm"
include "ax-r2.mm"
include "dff.mm"
include "ran.mm"
include "3tr2.mm"
include "bi1.mm"

theorem ska8
  param wva: term a
  param wvb: term b


  assert |- ( ( a ' ^ a ) == ( ( a ' ^ a ) ^ b ) ) = 1

  proof
    wva
    wn
    #
    wva
    wa
    #
    @1
    wvb
    wa
    #
    wf
    wf
    wvb
    wa
    #
    @1
    @2
    wf
    wvb
    wf
    wa
    #
    @3
    @4
    wf
    wvb
    an0
    ax-r1
    wvb
    wf
    ancom
    ax-r2
    wf
    wva
    @0
    wa
    @1
    wva
    dff
    wva
    @0
    ancom
    ax-r2
    #
    wf
    @1
    wvb
    @5
    ran
    3tr2
    bi1
end
