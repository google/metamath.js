include "caddc.mm"
include "cc.mm"
include "cc0.mm"
include "cv.mm"
include "cneg.mm"
include "cnex.mm"
include "ax-addf.mm"
include "addass.mm"
include "0cn.mm"
include "addid2.mm"
include "negcl.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "addcom.mm"
include "mpdan.mm"
include "negid.mm"
include "eqtr3d.mm"
include "isgrpoi.mm"
include "cxp.mm"
include "fdmi.mm"
include "isabloi.mm"

theorem cnaddabloOLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- + e. AbelOp

  proof
    vx
    vy
    caddc
    cc
    vx
    vy
    vz
    cc0
    caddc
    vx
    cv
    #
    cneg
    #
    cc
    cnex
    ax-addf
    @0
    vy
    cv
    #
    vz
    cv
    addass
    0cn
    @0
    addid2
    @0
    negcl
    #
    @0
    cc
    wcel
    #
    @0
    @1
    caddc
    co
    #
    @1
    @0
    caddc
    co
    #
    cc0
    @4
    @1
    cc
    wcel
    @5
    @6
    wceq
    @3
    @0
    @1
    addcom
    mpdan
    @0
    negid
    eqtr3d
    isgrpoi
    cc
    cc
    cxp
    cc
    caddc
    ax-addf
    fdmi
    @0
    @2
    addcom
    isabloi
end
