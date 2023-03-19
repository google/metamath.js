include "cc.mm"
include "caddc.mm"
include "cv.mm"
include "cneg.mm"
include "cc0.mm"
include "cvv.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cnex.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "cplusg.mm"
include "addex.mm"
include "grpplusg.mm"
include "addcl.mm"
include "addass.mm"
include "0cn.mm"
include "addid2.mm"
include "negcl.mm"
include "co.mm"
include "addcom.mm"
include "mpdan.mm"
include "negid.mm"
include "eqtr3d.mm"
include "isgrpi.mm"
include "isabli.mm"

theorem cnaddabl
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cnaddabl.g: |- G = { <. ( Base ` ndx ) , CC >. , <. ( +g ` ndx ) , + >. }


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
    cc
    cvv
    wcel
    cc
    cG
    cbs
    cfv
    wceq
    cnex
    cc
    caddc
    cG
    cvv
    cnaddabl.g
    grpbase
    ax-mp
    #
    caddc
    cvv
    wcel
    caddc
    cG
    cplusg
    cfv
    wceq
    addex
    cc
    caddc
    cG
    cvv
    cnaddabl.g
    grpplusg
    ax-mp
    #
    @0
    vy
    cv
    #
    addcl
    @0
    @4
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
    @6
    @1
    cc
    wcel
    @7
    @8
    wceq
    @5
    @0
    @1
    addcom
    mpdan
    @0
    negid
    eqtr3d
    isgrpi
    @2
    @3
    @0
    @4
    addcom
    isabli
end
