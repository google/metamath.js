include "chio.mm"
include "cho.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wf1o.mm"
include "hoif.mm"
include "f1of.mm"
include "ax-mp.mm"
include "hoival.mm"
include "eqcomd.mm"
include "oveqan12d.mm"
include "rgen2a.mm"
include "elhmop.mm"
include "mpbir2an.mm"

theorem idhmop
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- Iop e. HrmOp

  proof
    chio
    cho
    wcel
    chil
    chil
    chio
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    chio
    cfv
    #
    csp
    co
    @1
    chio
    cfv
    #
    @2
    csp
    co
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    chil
    chil
    chio
    wf1o
    @0
    hoif
    chil
    chil
    chio
    f1of
    ax-mp
    @5
    vx
    vy
    chil
    @1
    chil
    wcel
    #
    @2
    chil
    wcel
    @1
    @4
    @3
    @2
    csp
    @6
    @4
    @1
    @1
    hoival
    eqcomd
    @2
    hoival
    oveqan12d
    rgen2a
    vx
    vy
    chio
    elhmop
    mpbir2an
end
