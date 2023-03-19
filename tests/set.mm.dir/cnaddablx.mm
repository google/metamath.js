include "cc.mm"
include "caddc.mm"
include "cv.mm"
include "cneg.mm"
include "cc0.mm"
include "cnex.mm"
include "addex.mm"
include "addcl.mm"
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
include "isgrpix.mm"
include "grpbasex.mm"
include "grpplusgx.mm"
include "isabli.mm"

theorem cnaddablx
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cnaddablx.g: |- G = { <. 1 , CC >. , <. 2 , + >. }


  assert |- G e. Abel

  proof
    vx
    vy
    cc
    caddc
    cG
    vx
    vy
    vz
    cc
    caddc
    cG
    vx
    cv
    #
    cneg
    #
    cc0
    cnex
    addex
    cnaddablx.g
    @0
    vy
    cv
    #
    addcl
    @0
    @2
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
    isgrpix
    cc
    caddc
    cG
    cnex
    addex
    cnaddablx.g
    grpbasex
    cc
    caddc
    cG
    cnex
    addex
    cnaddablx.g
    grpplusgx
    @0
    @2
    addcom
    isabli
end
