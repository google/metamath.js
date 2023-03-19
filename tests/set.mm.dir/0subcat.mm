include "ccat.mm"
include "wcel.mm"
include "c0.mm"
include "csubc.mm"
include "cfv.mm"
include "chomf.mm"
include "cssc.mm"
include "wbr.mm"
include "cv.mm"
include "ccid.mm"
include "co.mm"
include "cop.mm"
include "cco.mm"
include "wral.mm"
include "wa.mm"
include "0ssc.mm"
include "ral0.mm"
include "a1i.mm"
include "eqid.mm"
include "id.mm"
include "cxp.mm"
include "wfn.mm"
include "wf.mm"
include "f0.mm"
include "ffn.mm"
include "ax-mp.mm"
include "0xp.mm"
include "fneq2i.mm"
include "mpbir.mm"
include "issubc2.mm"
include "mpbir2and.mm"

theorem 0subcat
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( C e. Cat -> (/) e. ( Subcat ` C ) )

  proof
    cC
    ccat
    wcel
    #
    c0
    cC
    csubc
    cfv
    wcel
    c0
    cC
    chomf
    cfv
    #
    cssc
    wbr
    vx
    cv
    #
    cC
    ccid
    cfv
    #
    cfv
    @2
    @2
    c0
    co
    wcel
    vg
    cv
    vf
    cv
    @2
    vy
    cv
    #
    cop
    vz
    cv
    #
    cC
    cco
    cfv
    #
    co
    co
    @2
    @5
    c0
    co
    wcel
    vg
    @4
    @5
    c0
    co
    wral
    vf
    @2
    @4
    c0
    co
    wral
    vz
    c0
    wral
    vy
    c0
    wral
    wa
    #
    vx
    c0
    wral
    #
    cC
    0ssc
    @8
    @0
    @7
    vx
    ral0
    a1i
    @0
    vx
    vy
    vz
    cC
    c0
    @6
    @3
    vf
    vg
    @1
    c0
    @1
    eqid
    @3
    eqid
    @6
    eqid
    @0
    id
    c0
    c0
    c0
    cxp
    #
    wfn
    #
    @0
    @10
    c0
    c0
    wfn
    #
    c0
    c0
    c0
    wf
    @11
    c0
    f0
    c0
    c0
    c0
    ffn
    ax-mp
    @9
    c0
    c0
    c0
    0xp
    fneq2i
    mpbir
    a1i
    issubc2
    mpbir2and
end
