include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wne.mm"
include "cn.mm"
include "wrex.mm"
include "cmnd.mm"
include "wnel.mm"
include "cc.mm"
include "wss.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "nnsscn.mm"
include "cnfldsrngbas.mm"
include "ax-mp.mm"
include "cvv.mm"
include "wcel.mm"
include "cplusg.mm"
include "nnex.mm"
include "cnfldsrngadd.mm"
include "isnmnd.mm"
include "c1.mm"
include "1nn.mm"
include "a1i.mm"
include "wb.mm"
include "oveq2.mm"
include "id.mm"
include "neeq12d.mm"
include "adantl.mm"
include "cc0.mm"
include "nnne0.mm"
include "necomd.mm"
include "cmin.mm"
include "1cnd.mm"
include "nncn.mm"
include "subadd2d.mm"
include "1m1e0.mm"
include "eqeq1d.mm"
include "bitr3d.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "rspcedvd.mm"
include "mprg.mm"

theorem nnsgrpnmnd
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume nnsgrp.m: |- M = ( CCfld |`s NN )


  assert |- M e/ Mnd

  proof
    vz
    cv
    #
    vx
    cv
    #
    caddc
    co
    #
    @1
    wne
    #
    vx
    cn
    wrex
    cM
    cmnd
    wnel
    vz
    cn
    vx
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
    isnmnd
    @0
    cn
    wcel
    #
    @3
    @0
    c1
    caddc
    co
    #
    c1
    wne
    #
    vx
    c1
    cn
    c1
    cn
    wcel
    @4
    1nn
    a1i
    @1
    c1
    wceq
    #
    @3
    @6
    wb
    @4
    @7
    @2
    @5
    @1
    c1
    @1
    c1
    @0
    caddc
    oveq2
    @7
    id
    neeq12d
    adantl
    @4
    @6
    cc0
    @0
    wne
    @4
    @0
    cc0
    @0
    nnne0
    necomd
    @4
    @5
    c1
    cc0
    @0
    @4
    c1
    c1
    cmin
    co
    #
    @0
    wceq
    @5
    c1
    wceq
    cc0
    @0
    wceq
    @4
    c1
    c1
    @0
    @4
    1cnd
    #
    @9
    @0
    nncn
    subadd2d
    @4
    @8
    cc0
    @0
    @8
    cc0
    wceq
    @4
    1m1e0
    a1i
    eqeq1d
    bitr3d
    necon3bid
    mpbird
    rspcedvd
    mprg
end
