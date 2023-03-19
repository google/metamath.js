include "zring.mm"
include "ccyg.mm"
include "wcel.mm"
include "wtru.mm"
include "cz.mm"
include "cmg.mm"
include "cfv.mm"
include "c1.mm"
include "zringbas.mm"
include "eqid.mm"
include "ccnfld.mm"
include "csubg.mm"
include "cgrp.mm"
include "csubrg.mm"
include "zsubrg.mm"
include "subrgsubg.mm"
include "ax-mp.mm"
include "df-zring.mm"
include "subggrp.mm"
include "mp1i.mm"
include "1zzd.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cmul.mm"
include "cc.mm"
include "ax-1cn.mm"
include "cnfldmulg.mm"
include "mpan2.mm"
include "1z.mm"
include "subgmulg.mm"
include "mp3an13.mm"
include "zcn.mm"
include "mulid1d.mm"
include "3eqtr3rd.mm"
include "weq.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpdan.mm"
include "adantl.mm"
include "iscygd.mm"
include "trud.mm"

theorem zringcyg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ZZring e. CycGrp

  proof
    zring
    ccyg
    wcel
    wtru
    vx
    cz
    zring
    cmg
    cfv
    #
    vz
    zring
    c1
    zringbas
    @0
    eqid
    #
    cz
    ccnfld
    csubg
    cfv
    wcel
    #
    zring
    cgrp
    wcel
    wtru
    cz
    ccnfld
    csubrg
    cfv
    wcel
    @2
    zsubrg
    cz
    ccnfld
    subrgsubg
    ax-mp
    #
    cz
    ccnfld
    zring
    df-zring
    subggrp
    mp1i
    wtru
    1zzd
    vx
    cv
    #
    cz
    wcel
    #
    @4
    vz
    cv
    #
    c1
    @0
    co
    #
    wceq
    #
    vz
    cz
    wrex
    #
    wtru
    @5
    @4
    @4
    c1
    @0
    co
    #
    wceq
    #
    @9
    @5
    @4
    c1
    ccnfld
    cmg
    cfv
    #
    co
    #
    @4
    c1
    cmul
    co
    #
    @10
    @4
    @5
    c1
    cc
    wcel
    @13
    @14
    wceq
    ax-1cn
    @4
    c1
    cnfldmulg
    mpan2
    @2
    @5
    c1
    cz
    wcel
    @13
    @10
    wceq
    @3
    1z
    cz
    @0
    @12
    ccnfld
    zring
    @4
    c1
    @12
    eqid
    df-zring
    @1
    subgmulg
    mp3an13
    @5
    @4
    @4
    zcn
    mulid1d
    3eqtr3rd
    @8
    @11
    vz
    @4
    cz
    vz
    vx
    weq
    @7
    @10
    @4
    @6
    @4
    c1
    @0
    oveq1
    eqeq2d
    rspcev
    mpdan
    adantl
    iscygd
    trud
end
