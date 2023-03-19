include "cpjh.mm"
include "cfv.mm"
include "cho.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "pjfi.mm"
include "wa.mm"
include "pjadji.mm"
include "eqcomd.mm"
include "rgen2a.mm"
include "elhmop.mm"
include "mpbir2an.mm"

theorem pjhmopi
  let cH: class H
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pjhmop.1: |- H e. CH


  assert |- ( projh ` H ) e. HrmOp

  proof
    cH
    cpjh
    cfv
    #
    cho
    wcel
    chil
    chil
    @0
    wf
    vx
    cv
    #
    vy
    cv
    #
    @0
    cfv
    csp
    co
    #
    @1
    @0
    cfv
    @2
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    cH
    pjhmop.1
    pjfi
    @5
    vx
    vy
    chil
    @1
    chil
    wcel
    @2
    chil
    wcel
    wa
    @4
    @3
    @1
    @2
    cH
    pjhmop.1
    pjadji
    eqcomd
    rgen2a
    vx
    vy
    @0
    elhmop
    mpbir2an
end
