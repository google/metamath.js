include "ccnfld.mm"
include "ccrg.mm"
include "wcel.mm"
include "wtru.mm"
include "cc.mm"
include "caddc.mm"
include "cmul.mm"
include "c1.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cnfldbas.mm"
include "a1i.mm"
include "cplusg.mm"
include "cnfldadd.mm"
include "cmulr.mm"
include "cnfldmul.mm"
include "cgrp.mm"
include "cv.mm"
include "cneg.mm"
include "cc0.mm"
include "addcl.mm"
include "addass.mm"
include "0cn.mm"
include "addid2.mm"
include "negcl.mm"
include "co.mm"
include "addcom.mm"
include "mpancom.mm"
include "negid.mm"
include "eqtrd.mm"
include "isgrpi.mm"
include "mulcl.mm"
include "3adant1.mm"
include "w3a.mm"
include "mulass.mm"
include "adantl.mm"
include "adddi.mm"
include "adddir.mm"
include "1cnd.mm"
include "mulid2.mm"
include "mulid1.mm"
include "mulcom.mm"
include "iscrngd.mm"
include "trud.mm"

theorem cncrng
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- CCfld e. CRing

  proof
    ccnfld
    ccrg
    wcel
    wtru
    vx
    vy
    vz
    cc
    caddc
    ccnfld
    cmul
    c1
    cc
    ccnfld
    cbs
    cfv
    wceq
    wtru
    cnfldbas
    a1i
    caddc
    ccnfld
    cplusg
    cfv
    wceq
    wtru
    cnfldadd
    a1i
    cmul
    ccnfld
    cmulr
    cfv
    wceq
    wtru
    cnfldmul
    a1i
    ccnfld
    cgrp
    wcel
    wtru
    vx
    vy
    vz
    cc
    caddc
    ccnfld
    vx
    cv
    #
    cneg
    #
    cc0
    cnfldbas
    cnfldadd
    @0
    vy
    cv
    #
    addcl
    @0
    @2
    vz
    cv
    #
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
    @1
    @0
    caddc
    co
    #
    @0
    @1
    caddc
    co
    #
    cc0
    @1
    cc
    wcel
    @5
    @6
    @7
    wceq
    @4
    @1
    @0
    addcom
    mpancom
    @0
    negid
    eqtrd
    isgrpi
    a1i
    @5
    @2
    cc
    wcel
    #
    @0
    @2
    cmul
    co
    #
    cc
    wcel
    wtru
    @0
    @2
    mulcl
    3adant1
    @5
    @8
    @3
    cc
    wcel
    w3a
    #
    @9
    @3
    cmul
    co
    @0
    @2
    @3
    cmul
    co
    #
    cmul
    co
    wceq
    wtru
    @0
    @2
    @3
    mulass
    adantl
    @10
    @0
    @2
    @3
    caddc
    co
    cmul
    co
    @9
    @0
    @3
    cmul
    co
    #
    caddc
    co
    wceq
    wtru
    @0
    @2
    @3
    adddi
    adantl
    @10
    @0
    @2
    caddc
    co
    @3
    cmul
    co
    @12
    @11
    caddc
    co
    wceq
    wtru
    @0
    @2
    @3
    adddir
    adantl
    wtru
    1cnd
    @5
    c1
    @0
    cmul
    co
    @0
    wceq
    wtru
    @0
    mulid2
    adantl
    @5
    @0
    c1
    cmul
    co
    @0
    wceq
    wtru
    @0
    mulid1
    adantl
    @5
    @8
    @9
    @2
    @0
    cmul
    co
    wceq
    wtru
    @0
    @2
    mulcom
    3adant1
    iscrngd
    trud
end
