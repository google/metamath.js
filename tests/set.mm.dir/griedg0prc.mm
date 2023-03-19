include "cvv.mm"
include "wnel.mm"
include "c0.mm"
include "cv.mm"
include "wf.mm"
include "copab.mm"
include "wex.mm"
include "0ex.mm"
include "feq1.mm"
include "f0.mm"
include "ceqsexv2d.mm"
include "opabn1stprc.mm"
include "ax-mp.mm"
include "wceq.mm"
include "wb.mm"
include "neleq1.mm"
include "mpbir.mm"

theorem griedg0prc
  let vv: setvar v
  let cU: class U
  let ve: setvar e
  assume griedg0prc.u: |- U = { <. v , e >. | e : (/) --> (/) }

  disjoint e v
  assert |- U e/ _V

  proof
    cU
    cvv
    wnel
    #
    c0
    c0
    ve
    cv
    #
    wf
    #
    vv
    ve
    copab
    #
    cvv
    wnel
    #
    @2
    ve
    wex
    @4
    @2
    c0
    c0
    c0
    wf
    ve
    c0
    0ex
    c0
    c0
    @1
    c0
    feq1
    c0
    f0
    ceqsexv2d
    @2
    vv
    ve
    opabn1stprc
    ax-mp
    cU
    @3
    wceq
    @0
    @4
    wb
    griedg0prc.u
    cU
    @3
    cvv
    neleq1
    ax-mp
    mpbir
end
