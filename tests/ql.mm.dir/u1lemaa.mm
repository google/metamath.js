include "wi1.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "df-i1.mm"
include "ran.mm"
include "comid.mm"
include "comcom2.mm"
include "comanr1.mm"
include "fh1r.mm"
include "wf.mm"
include "ax-a2.mm"
include "an32.mm"
include "anidm.mm"
include "ax-r2.mm"
include "ancom.mm"
include "dff.mm"
include "ax-r1.mm"
include "2or.mm"
include "or0.mm"

theorem u1lemaa
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->1 b ) ^ a ) = ( a ^ b )

  proof
    wva
    wvb
    wi1
    #
    wva
    wa
    wva
    wn
    #
    wva
    wvb
    wa
    #
    wo
    #
    wva
    wa
    #
    @2
    @0
    @3
    wva
    wva
    wvb
    df-i1
    ran
    @4
    @1
    wva
    wa
    #
    @2
    wva
    wa
    #
    wo
    #
    @2
    wva
    @1
    @2
    wva
    wva
    wva
    comid
    comcom2
    wva
    wvb
    comanr1
    fh1r
    @7
    @2
    wf
    wo
    #
    @2
    @7
    @6
    @5
    wo
    @8
    @5
    @6
    ax-a2
    @6
    @2
    @5
    wf
    @6
    wva
    wva
    wa
    #
    wvb
    wa
    @2
    wva
    wvb
    wva
    an32
    @9
    wva
    wvb
    wva
    anidm
    ran
    ax-r2
    @5
    wva
    @1
    wa
    #
    wf
    @1
    wva
    ancom
    wf
    @10
    wva
    dff
    ax-r1
    ax-r2
    2or
    ax-r2
    @2
    or0
    ax-r2
    ax-r2
    ax-r2
end
