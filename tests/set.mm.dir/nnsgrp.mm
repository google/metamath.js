include "csgrp.mm"
include "wcel.mm"
include "cmgm.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cn.mm"
include "wral.mm"
include "nnsgrpmgm.mm"
include "wa.mm"
include "cc.mm"
include "nncn.mm"
include "addass.mm"
include "syl3an.mm"
include "3expia.mm"
include "ralrimiv.mm"
include "rgen2a.mm"
include "wss.mm"
include "cbs.mm"
include "cfv.mm"
include "nnsscn.mm"
include "cnfldsrngbas.mm"
include "ax-mp.mm"
include "cvv.mm"
include "cplusg.mm"
include "nnex.mm"
include "cnfldsrngadd.mm"
include "issgrp.mm"
include "mpbir2an.mm"

theorem nnsgrp
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume nnsgrp.m: |- M = ( CCfld |`s NN )


  assert |- M e. SGrp

  proof
    cM
    csgrp
    wcel
    cM
    cmgm
    wcel
    vx
    cv
    #
    vy
    cv
    #
    caddc
    co
    vz
    cv
    #
    caddc
    co
    @0
    @1
    @2
    caddc
    co
    caddc
    co
    wceq
    #
    vz
    cn
    wral
    #
    vy
    cn
    wral
    vx
    cn
    wral
    cM
    nnsgrp.m
    nnsgrpmgm
    @4
    vx
    vy
    cn
    @0
    cn
    wcel
    #
    @1
    cn
    wcel
    #
    wa
    @3
    vz
    cn
    @5
    @6
    @2
    cn
    wcel
    #
    @3
    @5
    @0
    cc
    wcel
    @6
    @1
    cc
    wcel
    @7
    @2
    cc
    wcel
    @3
    @0
    nncn
    @1
    nncn
    @2
    nncn
    @0
    @1
    @2
    addass
    syl3an
    3expia
    ralrimiv
    rgen2a
    vx
    vy
    vz
    cn
    cM
    caddc
    cn
    cc
    wss
    cn
    cM
    cbs
    cfv
    wceq
    nnsscn
    cM
    cn
    nnsgrp.m
    cnfldsrngbas
    ax-mp
    cn
    cvv
    wcel
    caddc
    cM
    cplusg
    cfv
    wceq
    nnex
    cM
    cn
    cvv
    nnsgrp.m
    cnfldsrngadd
    ax-mp
    issgrp
    mpbir2an
end
