include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "crio.mm"
include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "cmin.mm"
include "wf.mm"
include "wa.mm"
include "subval.mm"
include "subcl.mm"
include "eqeltrrd.mm"
include "rgen2a.mm"
include "df-sub.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem subf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- - : ( CC X. CC ) --> CC

  proof
    vy
    cv
    #
    vz
    cv
    caddc
    co
    vx
    cv
    #
    wceq
    vz
    cc
    crio
    #
    cc
    wcel
    #
    vy
    cc
    wral
    vx
    cc
    wral
    cc
    cc
    cxp
    cc
    cmin
    wf
    @3
    vx
    vy
    cc
    @1
    cc
    wcel
    @0
    cc
    wcel
    wa
    @1
    @0
    cmin
    co
    @2
    cc
    vz
    @1
    @0
    subval
    @1
    @0
    subcl
    eqeltrrd
    rgen2a
    vx
    vy
    cc
    cc
    @2
    cc
    cmin
    vx
    vy
    vz
    df-sub
    fmpt2
    mpbi
end
