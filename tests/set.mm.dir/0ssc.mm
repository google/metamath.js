include "ccat.mm"
include "wcel.mm"
include "c0.mm"
include "chomf.mm"
include "cfv.mm"
include "cssc.mm"
include "wbr.mm"
include "cbs.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "0ss.mm"
include "a1i.mm"
include "ral0.mm"
include "cvv.mm"
include "cxp.mm"
include "wfn.mm"
include "wf.mm"
include "f0.mm"
include "ffn.mm"
include "ax-mp.mm"
include "xp0.mm"
include "fneq2i.mm"
include "mpbir.mm"
include "eqid.mm"
include "homffn.mm"
include "fvexd.mm"
include "isssc.mm"
include "mpbir2and.mm"

theorem 0ssc
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( C e. Cat -> (/) C_cat ( Homf ` C ) )

  proof
    cC
    ccat
    wcel
    #
    c0
    cC
    chomf
    cfv
    #
    cssc
    wbr
    c0
    cC
    cbs
    cfv
    #
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    c0
    co
    @4
    @5
    @1
    co
    wss
    vy
    c0
    wral
    #
    vx
    c0
    wral
    #
    @3
    @0
    @2
    0ss
    a1i
    @7
    @0
    @6
    vx
    ral0
    a1i
    @0
    vx
    vy
    c0
    @2
    c0
    @1
    cvv
    c0
    c0
    c0
    cxp
    #
    wfn
    #
    @0
    @9
    c0
    c0
    wfn
    #
    c0
    c0
    c0
    wf
    @10
    c0
    f0
    c0
    c0
    c0
    ffn
    ax-mp
    @8
    c0
    c0
    c0
    xp0
    fneq2i
    mpbir
    a1i
    @1
    @2
    @2
    cxp
    wfn
    @0
    @2
    cC
    @1
    @1
    eqid
    @2
    eqid
    homffn
    a1i
    @0
    cC
    cbs
    fvexd
    isssc
    mpbir2and
end
