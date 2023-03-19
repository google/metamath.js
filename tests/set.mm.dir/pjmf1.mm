include "cch.mm"
include "chil.mm"
include "cmap.mm"
include "co.mm"
include "cpjh.mm"
include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wfn.mm"
include "wcel.mm"
include "pjmfn.mm"
include "pjhf.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "sylibr.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"
include "wa.mm"
include "pj11.mm"
include "biimpd.mm"
include "rgen2a.mm"
include "dff13.mm"

theorem pjmf1
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- projh : CH -1-1-> ( ~H ^m ~H )

  proof
    cch
    chil
    chil
    cmap
    co
    #
    cpjh
    wf1
    cch
    @0
    cpjh
    wf
    #
    vx
    cv
    #
    cpjh
    cfv
    #
    vy
    cv
    #
    cpjh
    cfv
    wceq
    #
    @2
    @4
    wceq
    #
    wi
    #
    vy
    cch
    wral
    vx
    cch
    wral
    @1
    cpjh
    cch
    wfn
    @3
    @0
    wcel
    #
    vx
    cch
    wral
    pjmfn
    @8
    vx
    cch
    @2
    cch
    wcel
    #
    chil
    chil
    @3
    wf
    @8
    @2
    pjhf
    chil
    chil
    @3
    ax-hilex
    ax-hilex
    elmap
    sylibr
    rgen
    vx
    cch
    @0
    cpjh
    ffnfv
    mpbir2an
    @7
    vx
    vy
    cch
    @9
    @4
    cch
    wcel
    wa
    @5
    @6
    @2
    @4
    pj11
    biimpd
    rgen2a
    vx
    vy
    cch
    @0
    cpjh
    dff13
    mpbir2an
end
