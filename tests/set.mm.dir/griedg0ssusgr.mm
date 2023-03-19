include "cusgr.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wceq.mm"
include "c0.mm"
include "wf.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "eleq2i.mm"
include "elopab.mm"
include "bitri.mm"
include "cvv.mm"
include "opex.mm"
include "a1i.mm"
include "ciedg.mm"
include "cfv.mm"
include "vex.mm"
include "opiedgfv.mm"
include "mp2an.mm"
include "f0bi.mm"
include "biimpi.mm"
include "syl5eq.mm"
include "usgr0e.mm"
include "adantl.mm"
include "wb.mm"
include "eleq1.mm"
include "adantr.mm"
include "mpbird.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "ssriv.mm"

theorem griedg0ssusgr
  let vv: setvar v
  let cU: class U
  let ve: setvar e
  let vg: setvar g
  assume griedg0prc.u: |- U = { <. v , e >. | e : (/) --> (/) }

  disjoint e v
  disjoint e g
  disjoint g v
  disjoint U g
  assert |- U C_ USGraph

  proof
    vg
    cU
    cusgr
    vg
    cv
    #
    cU
    wcel
    #
    @0
    vv
    cv
    #
    ve
    cv
    #
    cop
    #
    wceq
    #
    c0
    c0
    @3
    wf
    #
    wa
    #
    ve
    wex
    vv
    wex
    #
    @0
    cusgr
    wcel
    #
    @1
    @0
    @6
    vv
    ve
    copab
    #
    wcel
    @8
    cU
    @10
    @0
    griedg0prc.u
    eleq2i
    @6
    vv
    ve
    @0
    elopab
    bitri
    @7
    @9
    vv
    ve
    @7
    @9
    @4
    cusgr
    wcel
    #
    @6
    @11
    @5
    @6
    @4
    cvv
    @4
    cvv
    wcel
    @6
    @2
    @3
    opex
    a1i
    @6
    @4
    ciedg
    cfv
    #
    @3
    c0
    @2
    cvv
    wcel
    @3
    cvv
    wcel
    @12
    @3
    wceq
    vv
    vex
    ve
    vex
    @3
    @2
    cvv
    cvv
    opiedgfv
    mp2an
    @6
    @3
    c0
    wceq
    @3
    c0
    f0bi
    biimpi
    syl5eq
    usgr0e
    adantl
    @5
    @9
    @11
    wb
    @6
    @0
    @4
    cusgr
    eleq1
    adantr
    mpbird
    exlimivv
    sylbi
    ssriv
end
