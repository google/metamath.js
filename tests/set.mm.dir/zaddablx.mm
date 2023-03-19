include "cz.mm"
include "caddc.mm"
include "cv.mm"
include "cneg.mm"
include "cc0.mm"
include "zex.mm"
include "addex.mm"
include "zaddcl.mm"
include "wcel.mm"
include "cc.mm"
include "co.mm"
include "wceq.mm"
include "zcn.mm"
include "addass.mm"
include "syl3an.mm"
include "0z.mm"
include "addid2d.mm"
include "znegcl.mm"
include "addcom.mm"
include "syl2an.mm"
include "mpdan.mm"
include "negidd.mm"
include "eqtr3d.mm"
include "isgrpix.mm"
include "grpbasex.mm"
include "grpplusgx.mm"
include "isabli.mm"

theorem zaddablx
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume zaddablx.g: |- G = { <. 1 , ZZ >. , <. 2 , + >. }


  assert |- G e. Abel

  proof
    vx
    vy
    cz
    caddc
    cG
    vx
    vy
    vz
    cz
    caddc
    cG
    vx
    cv
    #
    cneg
    #
    cc0
    zex
    addex
    zaddablx.g
    @0
    vy
    cv
    #
    zaddcl
    @0
    cz
    wcel
    #
    @0
    cc
    wcel
    #
    @2
    cz
    wcel
    #
    @2
    cc
    wcel
    #
    vz
    cv
    #
    cz
    wcel
    @7
    cc
    wcel
    @0
    @2
    caddc
    co
    #
    @7
    caddc
    co
    @0
    @2
    @7
    caddc
    co
    caddc
    co
    wceq
    @0
    zcn
    #
    @2
    zcn
    #
    @7
    zcn
    @0
    @2
    @7
    addass
    syl3an
    0z
    @3
    @0
    @9
    addid2d
    @0
    znegcl
    #
    @3
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
    @3
    @1
    cz
    wcel
    #
    @12
    @13
    wceq
    #
    @11
    @3
    @4
    @1
    cc
    wcel
    @15
    @14
    @9
    @1
    zcn
    @0
    @1
    addcom
    syl2an
    mpdan
    @3
    @0
    @9
    negidd
    eqtr3d
    isgrpix
    cz
    caddc
    cG
    zex
    addex
    zaddablx.g
    grpbasex
    cz
    caddc
    cG
    zex
    addex
    zaddablx.g
    grpplusgx
    @3
    @4
    @6
    @8
    @2
    @0
    caddc
    co
    wceq
    @5
    @9
    @10
    @0
    @2
    addcom
    syl2an
    isabli
end
