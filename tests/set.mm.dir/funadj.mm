include "cado.mm"
include "wfun.mm"
include "chil.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "copab.mm"
include "wmo.mm"
include "funopab.mm"
include "wa.mm"
include "adjmo.mm"
include "3simpc.mm"
include "moimi.mm"
include "ax-mp.mm"
include "mpgbir.mm"
include "dfadj2.mm"
include "funeqi.mm"
include "mpbir.mm"

theorem funadj
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cT: class T


  assert |- Fun adjh

  proof
    cado
    wfun
    chil
    chil
    vt
    cv
    #
    wf
    #
    chil
    chil
    vu
    cv
    #
    wf
    #
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
    @4
    @2
    cfv
    @5
    csp
    co
    wceq
    vy
    chil
    wral
    vx
    chil
    wral
    #
    w3a
    #
    vt
    vu
    copab
    #
    wfun
    #
    @9
    @7
    vu
    wmo
    #
    vt
    @7
    vt
    vu
    funopab
    @3
    @6
    wa
    #
    vu
    wmo
    @10
    vx
    vy
    vu
    @0
    adjmo
    @7
    @11
    vu
    @1
    @3
    @6
    3simpc
    moimi
    ax-mp
    mpgbir
    cado
    @8
    vx
    vy
    vu
    vt
    dfadj2
    funeqi
    mpbir
end
