include "cpjh.mm"
include "cfv.mm"
include "crn.mm"
include "chil.mm"
include "wf.mm"
include "wss.mm"
include "wfn.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "pjfni.mm"
include "pjcli.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"
include "frn.mm"
include "ax-mp.mm"
include "cch.mm"
include "wceq.mm"
include "pjid.mm"
include "mpan.mm"
include "cheli.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "eqeltrrd.mm"
include "ssriv.mm"
include "eqssi.mm"

theorem pjrni
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pjfn.1: |- H e. CH


  assert |- ran ( projh ` H ) = H

  proof
    cH
    cpjh
    cfv
    #
    crn
    #
    cH
    chil
    cH
    @0
    wf
    #
    @1
    cH
    wss
    @2
    @0
    chil
    wfn
    #
    vx
    cv
    #
    @0
    cfv
    cH
    wcel
    #
    vx
    chil
    wral
    cH
    pjfn.1
    pjfni
    #
    @5
    vx
    chil
    @4
    cH
    pjfn.1
    pjcli
    rgen
    vx
    chil
    cH
    @0
    ffnfv
    mpbir2an
    chil
    cH
    @0
    frn
    ax-mp
    vy
    cH
    @1
    vy
    cv
    #
    cH
    wcel
    #
    @7
    @0
    cfv
    #
    @7
    @1
    cH
    cch
    wcel
    @8
    @9
    @7
    wceq
    pjfn.1
    @7
    cH
    pjid
    mpan
    @8
    @3
    @7
    chil
    wcel
    @9
    @1
    wcel
    @6
    @7
    cH
    pjfn.1
    cheli
    chil
    @7
    @0
    fnfvelrn
    sylancr
    eqeltrrd
    ssriv
    eqssi
end
