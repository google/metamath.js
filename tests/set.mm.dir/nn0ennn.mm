include "cn0.mm"
include "cn.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "nn0ex.mm"
include "nnex.mm"
include "nn0p1nn.mm"
include "nnm1nn0.mm"
include "wcel.mm"
include "cc.mm"
include "wceq.mm"
include "wb.mm"
include "nncn.mm"
include "nn0cn.mm"
include "wa.mm"
include "ax-1cn.mm"
include "subadd.mm"
include "mp3an2.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "addcom.mm"
include "mpan.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "bitrd.mm"
include "syl2anr.mm"
include "en3i.mm"

theorem nn0ennn
  let vx: setvar x
  let vy: setvar y


  assert |- NN0 ~~ NN

  proof
    vx
    vy
    cn0
    cn
    vx
    cv
    #
    c1
    caddc
    co
    #
    vy
    cv
    #
    c1
    cmin
    co
    #
    nn0ex
    nnex
    @0
    nn0p1nn
    @2
    nnm1nn0
    @2
    cn
    wcel
    @2
    cc
    wcel
    #
    @0
    cc
    wcel
    #
    @0
    @3
    wceq
    #
    @2
    @1
    wceq
    #
    wb
    @0
    cn0
    wcel
    @2
    nncn
    @0
    nn0cn
    @4
    @5
    wa
    #
    @6
    @2
    c1
    @0
    caddc
    co
    #
    wceq
    #
    @7
    @8
    @3
    @0
    wceq
    #
    @9
    @2
    wceq
    #
    @6
    @10
    @4
    c1
    cc
    wcel
    #
    @5
    @11
    @12
    wb
    ax-1cn
    @2
    c1
    @0
    subadd
    mp3an2
    @0
    @3
    eqcom
    @2
    @9
    eqcom
    3bitr4g
    @5
    @10
    @7
    wb
    @4
    @5
    @9
    @1
    @2
    @13
    @5
    @9
    @1
    wceq
    ax-1cn
    c1
    @0
    addcom
    mpan
    eqeq2d
    adantl
    bitrd
    syl2anr
    en3i
end
