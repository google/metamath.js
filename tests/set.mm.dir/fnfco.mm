include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "ccom.mm"
include "df-f.mm"
include "fnco.mm"
include "3expb.mm"
include "sylan2b.mm"

theorem fnfco
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( ( F Fn A /\ G : B --> A ) -> ( F o. G ) Fn B )

  proof
    cB
    cA
    cG
    wf
    cF
    cA
    wfn
    #
    cG
    cB
    wfn
    #
    cG
    crn
    cA
    wss
    #
    wa
    cF
    cG
    ccom
    cB
    wfn
    #
    cB
    cA
    cG
    df-f
    @0
    @1
    @2
    @3
    cA
    cB
    cF
    cG
    fnco
    3expb
    sylan2b
end
