include "cc0.mm"
include "cc.mm"
include "wcel.mm"
include "cgrp.mm"
include "clmod.mm"
include "0cn.mm"
include "caddc.mm"
include "cv.mm"
include "cneg.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cnlmodlem1.mm"
include "eqcomi.mm"
include "a1i.mm"
include "cplusg.mm"
include "cnlmodlem2.mm"
include "co.mm"
include "addcl.mm"
include "3adant1.mm"
include "w3a.mm"
include "addass.mm"
include "adantl.mm"
include "id.mm"
include "addid2.mm"
include "negcl.mm"
include "wa.mm"
include "addcomd.mm"
include "negid.mm"
include "eqtrd.mm"
include "isgrpd.mm"
include "cmul.mm"
include "c1.mm"
include "ccnfld.mm"
include "csca.mm"
include "cnlmodlem3.mm"
include "cvsca.mm"
include "cnlmod4.mm"
include "cnfldbas.mm"
include "cnfldadd.mm"
include "cmulr.mm"
include "cnfldmul.mm"
include "cur.mm"
include "cnfld1.mm"
include "crg.mm"
include "cnring.mm"
include "mulcl.mm"
include "adddi.mm"
include "adddir.mm"
include "mulass.mm"
include "mulid2.mm"
include "islmodd.mm"
include "mp2b.mm"

theorem cnlmod
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cnlmod.w: |- W = ( { <. ( Base ` ndx ) , CC >. , <. ( +g ` ndx ) , + >. } u. { <. ( Scalar ` ndx ) , CCfld >. , <. ( .s ` ndx ) , x. >. } )


  assert |- W e. LMod

  proof
    cc0
    cc
    wcel
    #
    cW
    cgrp
    wcel
    #
    cW
    clmod
    wcel
    0cn
    @0
    vx
    vy
    vz
    cc
    caddc
    cW
    vx
    cv
    #
    cneg
    #
    cc0
    cc
    cW
    cbs
    cfv
    #
    wceq
    #
    @0
    @4
    cc
    cW
    cnlmod.w
    cnlmodlem1
    eqcomi
    #
    a1i
    caddc
    cW
    cplusg
    cfv
    #
    wceq
    #
    @0
    @7
    caddc
    cW
    cnlmod.w
    cnlmodlem2
    eqcomi
    #
    a1i
    @2
    cc
    wcel
    #
    vy
    cv
    #
    cc
    wcel
    #
    @2
    @11
    caddc
    co
    #
    cc
    wcel
    @0
    @2
    @11
    addcl
    3adant1
    @10
    @12
    vz
    cv
    #
    cc
    wcel
    w3a
    #
    @13
    @14
    caddc
    co
    @2
    @11
    @14
    caddc
    co
    #
    caddc
    co
    wceq
    @0
    @2
    @11
    @14
    addass
    adantl
    @0
    id
    @10
    cc0
    @2
    caddc
    co
    @2
    wceq
    @0
    @2
    addid2
    adantl
    @10
    @3
    cc
    wcel
    @0
    @2
    negcl
    #
    adantl
    @0
    @10
    wa
    @3
    @2
    caddc
    co
    #
    @2
    @3
    caddc
    co
    #
    cc0
    @10
    @18
    @19
    wceq
    @0
    @10
    @3
    @2
    @17
    @10
    id
    addcomd
    adantl
    @10
    @19
    cc0
    wceq
    @0
    @2
    negid
    adantl
    eqtrd
    isgrpd
    @1
    vx
    vy
    vz
    cc
    caddc
    caddc
    cmul
    cmul
    c1
    ccnfld
    cc
    cW
    @5
    @1
    @6
    a1i
    @8
    @1
    @9
    a1i
    ccnfld
    cW
    csca
    cfv
    #
    wceq
    @1
    @20
    ccnfld
    cW
    cnlmod.w
    cnlmodlem3
    eqcomi
    a1i
    cmul
    cW
    cvsca
    cfv
    #
    wceq
    @1
    @21
    cmul
    cW
    cnlmod.w
    cnlmod4
    eqcomi
    a1i
    cc
    ccnfld
    cbs
    cfv
    wceq
    @1
    cnfldbas
    a1i
    caddc
    ccnfld
    cplusg
    cfv
    wceq
    @1
    cnfldadd
    a1i
    cmul
    ccnfld
    cmulr
    cfv
    wceq
    @1
    cnfldmul
    a1i
    c1
    ccnfld
    cur
    cfv
    wceq
    @1
    cnfld1
    a1i
    ccnfld
    crg
    wcel
    @1
    cnring
    a1i
    @1
    id
    @10
    @12
    @2
    @11
    cmul
    co
    #
    cc
    wcel
    @1
    @2
    @11
    mulcl
    3adant1
    @15
    @2
    @16
    cmul
    co
    @22
    @2
    @14
    cmul
    co
    #
    caddc
    co
    wceq
    @1
    @2
    @11
    @14
    adddi
    adantl
    @15
    @13
    @14
    cmul
    co
    @23
    @11
    @14
    cmul
    co
    #
    caddc
    co
    wceq
    @1
    @2
    @11
    @14
    adddir
    adantl
    @15
    @22
    @14
    cmul
    co
    @2
    @24
    cmul
    co
    wceq
    @1
    @2
    @11
    @14
    mulass
    adantl
    @10
    c1
    @2
    cmul
    co
    @2
    wceq
    @1
    @2
    mulid2
    adantl
    islmodd
    mp2b
end
