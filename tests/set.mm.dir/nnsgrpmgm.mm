include "c1.mm"
include "cn.mm"
include "wcel.mm"
include "cmgm.mm"
include "1nn.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wral.mm"
include "nnaddcl.mm"
include "rgen2a.mm"
include "cc.mm"
include "wss.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "nnsscn.mm"
include "cnfldsrngbas.mm"
include "ax-mp.mm"
include "cvv.mm"
include "cplusg.mm"
include "nnex.mm"
include "cnfldsrngadd.mm"
include "ismgmn0.mm"
include "mpbiri.mm"

theorem nnsgrpmgm
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume nnsgrp.m: |- M = ( CCfld |`s NN )


  assert |- M e. Mgm

  proof
    c1
    cn
    wcel
    #
    cM
    cmgm
    wcel
    #
    1nn
    @0
    @1
    vx
    cv
    #
    vy
    cv
    #
    caddc
    co
    cn
    wcel
    #
    vy
    cn
    wral
    vx
    cn
    wral
    @4
    vx
    vy
    cn
    @2
    @3
    nnaddcl
    rgen2a
    vx
    vy
    c1
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
    ismgmn0
    mpbiri
    ax-mp
end
