include "cli.mm"
include "cdm.mm"
include "cc.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "climrel.mm"
include "climuni.mm"
include "ax-gen.mm"
include "dffun2.mm"
include "mpbir2an.mm"
include "funfn.mm"
include "mpbi.mm"
include "wcel.mm"
include "wex.mm"
include "vex.mm"
include "elrn.mm"
include "climcl.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "ssriv.mm"
include "df-f.mm"

theorem fclim
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ~~> : dom ~~> --> CC

  proof
    cli
    cdm
    #
    cc
    cli
    wf
    cli
    @0
    wfn
    #
    cli
    crn
    #
    cc
    wss
    cli
    wfun
    #
    @1
    @3
    cli
    wrel
    vx
    cv
    #
    vy
    cv
    #
    cli
    wbr
    #
    @4
    vz
    cv
    #
    cli
    wbr
    wa
    vy
    vz
    weq
    wi
    #
    vz
    wal
    #
    vy
    wal
    #
    vx
    wal
    climrel
    @10
    vx
    @9
    vy
    @8
    vz
    @5
    @7
    @4
    climuni
    ax-gen
    ax-gen
    ax-gen
    vx
    vy
    vz
    cli
    dffun2
    mpbir2an
    cli
    funfn
    mpbi
    vy
    @2
    cc
    @5
    @2
    wcel
    @6
    vx
    wex
    @5
    cc
    wcel
    #
    vx
    @5
    cli
    vy
    vex
    elrn
    @6
    @11
    vx
    @5
    @4
    climcl
    exlimiv
    sylbi
    ssriv
    @0
    cc
    cli
    df-f
    mpbir2an
end
