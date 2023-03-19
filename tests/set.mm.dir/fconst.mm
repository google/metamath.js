include "csn.mm"
include "cxp.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "fconstmpt.mm"
include "fnmpti.mm"
include "rnxpss.mm"
include "df-f.mm"
include "mpbir2an.mm"

theorem fconst
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume fconst.1: |- B e. _V


  assert |- ( A X. { B } ) : A --> { B }

  proof
    cA
    cB
    csn
    #
    cA
    @0
    cxp
    #
    wf
    @1
    cA
    wfn
    @1
    crn
    @0
    wss
    vx
    cA
    cB
    @1
    fconst.1
    vx
    cA
    cB
    fconstmpt
    fnmpti
    cA
    @0
    rnxpss
    cA
    @0
    @1
    df-f
    mpbir2an
end
