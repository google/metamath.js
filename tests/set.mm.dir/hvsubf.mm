include "cv.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "chil.mm"
include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "cmv.mm"
include "wf.mm"
include "cc.mm"
include "neg1cn.mm"
include "hvmulcl.mm"
include "mpan.mm"
include "hvaddcl.mm"
include "sylan2.mm"
include "rgen2a.mm"
include "df-hvsub.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem hvsubf
  let vx: setvar x
  let vy: setvar y


  assert |- -h : ( ~H X. ~H ) --> ~H

  proof
    vx
    cv
    #
    c1
    cneg
    #
    vy
    cv
    #
    csm
    co
    #
    cva
    co
    #
    chil
    wcel
    #
    vy
    chil
    wral
    vx
    chil
    wral
    chil
    chil
    cxp
    chil
    cmv
    wf
    @5
    vx
    vy
    chil
    @2
    chil
    wcel
    #
    @0
    chil
    wcel
    @3
    chil
    wcel
    #
    @5
    @1
    cc
    wcel
    @6
    @7
    neg1cn
    @1
    @2
    hvmulcl
    mpan
    @0
    @3
    hvaddcl
    sylan2
    rgen2a
    vx
    vy
    chil
    chil
    @4
    chil
    cmv
    vx
    vy
    df-hvsub
    fmpt2
    mpbi
end
