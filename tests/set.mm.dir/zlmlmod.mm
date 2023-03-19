include "cabl.mm"
include "wcel.mm"
include "clmod.mm"
include "cz.mm"
include "cplusg.mm"
include "cfv.mm"
include "caddc.mm"
include "cmg.mm"
include "cmul.mm"
include "c1.mm"
include "zring.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "zlmbas.mm"
include "a1i.mm"
include "zlmplusg.mm"
include "zlmsca.mm"
include "cvsca.mm"
include "zlmvsca.mm"
include "zringbas.mm"
include "zringplusg.mm"
include "cmulr.mm"
include "zringmulr.mm"
include "cur.mm"
include "zring1.mm"
include "crg.mm"
include "zringring.mm"
include "cgrp.mm"
include "ablprop.mm"
include "ablgrp.mm"
include "sylbi.mm"
include "cv.mm"
include "co.mm"
include "mulgcl.mm"
include "syl3an1.mm"
include "mulgdi.mm"
include "w3a.mm"
include "mulgdir.mm"
include "sylan.mm"
include "mulgass.mm"
include "mulg1.mm"
include "adantl.mm"
include "islmodd.mm"
include "lmodabl.mm"
include "sylibr.mm"
include "impbii.mm"

theorem zlmlmod
  let cG: class G
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume zlmlmod.w: |- W = ( ZMod ` G )


  assert |- ( G e. Abel <-> W e. LMod )

  proof
    cG
    cabl
    wcel
    #
    cW
    clmod
    wcel
    #
    @0
    vx
    vy
    vz
    cz
    cG
    cplusg
    cfv
    #
    caddc
    cG
    cmg
    cfv
    #
    cmul
    c1
    zring
    cG
    cbs
    cfv
    #
    cW
    @4
    cW
    cbs
    cfv
    wceq
    @0
    @4
    cG
    cW
    zlmlmod.w
    @4
    eqid
    #
    zlmbas
    #
    a1i
    @2
    cW
    cplusg
    cfv
    wceq
    @0
    @2
    cG
    cW
    zlmlmod.w
    @2
    eqid
    #
    zlmplusg
    #
    a1i
    cG
    cabl
    cW
    zlmlmod.w
    zlmsca
    @3
    cW
    cvsca
    cfv
    wceq
    @0
    @3
    cG
    cW
    zlmlmod.w
    @3
    eqid
    #
    zlmvsca
    a1i
    cz
    zring
    cbs
    cfv
    wceq
    @0
    zringbas
    a1i
    caddc
    zring
    cplusg
    cfv
    wceq
    @0
    zringplusg
    a1i
    cmul
    zring
    cmulr
    cfv
    wceq
    @0
    zringmulr
    a1i
    c1
    zring
    cur
    cfv
    wceq
    @0
    zring1
    a1i
    zring
    crg
    wcel
    @0
    zringring
    a1i
    @0
    cW
    cabl
    wcel
    #
    cW
    cgrp
    wcel
    cG
    cW
    @6
    @8
    ablprop
    #
    cW
    ablgrp
    sylbi
    @0
    cG
    cgrp
    wcel
    #
    vx
    cv
    #
    cz
    wcel
    #
    vy
    cv
    #
    @4
    wcel
    @13
    @15
    @3
    co
    @4
    wcel
    cG
    ablgrp
    #
    @4
    @3
    cG
    @13
    @15
    @5
    @9
    mulgcl
    syl3an1
    @4
    @2
    @3
    cG
    @13
    @15
    vz
    cv
    #
    @5
    @9
    @7
    mulgdi
    @0
    @12
    @14
    @15
    cz
    wcel
    @17
    @4
    wcel
    w3a
    #
    @13
    @15
    caddc
    co
    @17
    @3
    co
    @13
    @17
    @3
    co
    @15
    @17
    @3
    co
    #
    @2
    co
    wceq
    @16
    @4
    @2
    @3
    cG
    @13
    @15
    @17
    @5
    @9
    @7
    mulgdir
    sylan
    @0
    @12
    @18
    @13
    @15
    cmul
    co
    @17
    @3
    co
    @13
    @19
    @3
    co
    wceq
    @16
    @4
    @3
    cG
    @13
    @15
    @17
    @5
    @9
    mulgass
    sylan
    @13
    @4
    wcel
    c1
    @13
    @3
    co
    @13
    wceq
    @0
    @4
    @3
    cG
    @13
    @5
    @9
    mulg1
    adantl
    islmodd
    @1
    @10
    @0
    cW
    lmodabl
    @11
    sylibr
    impbii
end
