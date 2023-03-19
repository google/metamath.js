include "wcel.mm"
include "cnzr.mm"
include "wn.mm"
include "wnel.mm"
include "cbs.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "wceq.mm"
include "csn.mm"
include "cvv.mm"
include "snex.mm"
include "cop.mm"
include "rngbase.mm"
include "mp1i.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "hashsng.mm"
include "eqtrd.mm"
include "crg.mm"
include "wb.mm"
include "ring1.mm"
include "0ringnnzr.mm"
include "syl.mm"
include "mpbid.mm"
include "df-nel.mm"
include "sylibr.mm"

theorem rng1nnzr
  let cM: class M
  let cV: class V
  let cZ: class Z
  assume rng1nnzr.m: |- M = { <. ( Base ` ndx ) , { Z } >. , <. ( +g ` ndx ) , { <. <. Z , Z >. , Z >. } >. , <. ( .r ` ndx ) , { <. <. Z , Z >. , Z >. } >. }


  assert |- ( Z e. V -> M e/ NzRing )

  proof
    cZ
    cV
    wcel
    #
    cM
    cnzr
    wcel
    wn
    #
    cM
    cnzr
    wnel
    @0
    cM
    cbs
    cfv
    #
    chash
    cfv
    #
    c1
    wceq
    #
    @1
    @0
    @3
    cZ
    csn
    #
    chash
    cfv
    c1
    @0
    @2
    @5
    chash
    @0
    @5
    @2
    @5
    cvv
    wcel
    @5
    @2
    wceq
    @0
    cZ
    snex
    @5
    cZ
    cZ
    cop
    cZ
    cop
    csn
    #
    cM
    @6
    cvv
    rng1nnzr.m
    rngbase
    mp1i
    eqcomd
    fveq2d
    cZ
    cV
    hashsng
    eqtrd
    @0
    cM
    crg
    wcel
    @4
    @1
    wb
    cM
    cV
    cZ
    rng1nnzr.m
    ring1
    cM
    0ringnnzr
    syl
    mpbid
    cM
    cnzr
    df-nel
    sylibr
end
