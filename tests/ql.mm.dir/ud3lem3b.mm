include "wi3.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wf.mm"
include "ud3lem0c.mm"
include "ran.mm"
include "an32.mm"
include "anass.mm"
include "dff.mm"
include "ax-r1.mm"
include "lan.mm"
include "an0.mm"
include "ax-r2.mm"
include "an0r.mm"

theorem ud3lem3b
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->3 b ) ' ^ ( a v b ) ' ) = 0

  proof
    wva
    wvb
    wi3
    wn
    #
    wva
    wvb
    wo
    #
    wn
    #
    wa
    wva
    wvb
    wn
    #
    wo
    #
    @1
    wa
    #
    wva
    wn
    wva
    @3
    wa
    wo
    #
    wa
    #
    @2
    wa
    #
    wf
    @0
    @7
    @2
    wva
    wvb
    ud3lem0c
    ran
    @8
    @5
    @2
    wa
    #
    @6
    wa
    #
    wf
    @5
    @6
    @2
    an32
    @10
    wf
    @6
    wa
    wf
    @9
    wf
    @6
    @9
    @4
    @1
    @2
    wa
    #
    wa
    #
    wf
    @4
    @1
    @2
    anass
    @12
    @4
    wf
    wa
    wf
    @11
    wf
    @4
    wf
    @11
    @1
    dff
    ax-r1
    lan
    @4
    an0
    ax-r2
    ax-r2
    ran
    @6
    an0r
    ax-r2
    ax-r2
    ax-r2
end
