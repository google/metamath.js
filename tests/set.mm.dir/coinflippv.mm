include "csn.mm"
include "cfv.mm"
include "chash.mm"
include "cpr.mm"
include "cpw.mm"
include "cres.mm"
include "c2.mm"
include "cdiv.mm"
include "cofc.mm"
include "co.mm"
include "c1.mm"
include "fveq1i.mm"
include "wss.mm"
include "wcel.mm"
include "wceq.mm"
include "snsspr1.mm"
include "prex.mm"
include "elpw2.mm"
include "biimpri.mm"
include "cv.mm"
include "fveq2.mm"
include "cvv.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "cmpt.mm"
include "cn0.mm"
include "pwex.mm"
include "a1i.mm"
include "2nn0.mm"
include "wa.mm"
include "cfn.mm"
include "prfi.mm"
include "elpwi.mm"
include "ssfi.mm"
include "sylancr.mm"
include "adantl.mm"
include "hashcl.mm"
include "syl.mm"
include "cpnf.mm"
include "cun.mm"
include "wf.mm"
include "hashf.mm"
include "ssv.mm"
include "feqresmpt.mm"
include "ofcfval2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "mp2b.mm"
include "eqtri.mm"

theorem coinflippv
  let cP: class P
  let cT: class T
  let cH: class H
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume coinflip.h: |- H e. _V
  assume coinflip.t: |- T e. _V
  assume coinflip.th: |- H =/= T
  assume coinflip.2: |- P = ( ( # |` ~P { H , T } ) oFC / 2 )
  assume coinflip.3: |- X = { <. H , 1 >. , <. T , 0 >. }


  assert |- ( P ` { H } ) = ( 1 / 2 )

  proof
    cH
    csn
    #
    cP
    cfv
    @0
    chash
    cH
    cT
    cpr
    #
    cpw
    #
    cres
    #
    c2
    cdiv
    cofc
    co
    #
    cfv
    #
    c1
    c2
    cdiv
    co
    #
    @0
    cP
    @4
    coinflip.2
    fveq1i
    @0
    @1
    wss
    #
    @0
    @2
    wcel
    #
    @5
    @6
    wceq
    cH
    cT
    snsspr1
    @8
    @7
    @0
    @1
    cH
    cT
    prex
    #
    elpw2
    biimpri
    vx
    @0
    vx
    cv
    #
    chash
    cfv
    #
    c2
    cdiv
    co
    #
    @6
    @2
    @4
    @10
    @0
    wceq
    #
    @11
    c1
    c2
    cdiv
    @13
    @11
    @0
    chash
    cfv
    #
    c1
    @10
    @0
    chash
    fveq2
    cH
    cvv
    wcel
    #
    @14
    c1
    wceq
    coinflip.h
    cH
    cvv
    hashsng
    ax-mp
    syl6eq
    oveq1d
    @15
    @4
    vx
    @2
    @12
    cmpt
    wceq
    coinflip.h
    @15
    vx
    @2
    @11
    c2
    cdiv
    @3
    cvv
    cn0
    cn0
    @2
    cvv
    wcel
    @15
    @1
    @9
    pwex
    a1i
    c2
    cn0
    wcel
    @15
    2nn0
    a1i
    @15
    @10
    @2
    wcel
    #
    wa
    @10
    cfn
    wcel
    #
    @11
    cn0
    wcel
    @16
    @17
    @15
    @16
    @1
    cfn
    wcel
    @10
    @1
    wss
    @17
    cH
    cT
    prfi
    @10
    @1
    elpwi
    @1
    @10
    ssfi
    sylancr
    adantl
    @10
    hashcl
    syl
    @15
    vx
    cvv
    cn0
    cpnf
    csn
    cun
    #
    @2
    chash
    cvv
    @18
    chash
    wf
    @15
    hashf
    a1i
    @2
    cvv
    wss
    @15
    @2
    ssv
    a1i
    feqresmpt
    ofcfval2
    ax-mp
    c1
    c2
    cdiv
    ovex
    fvmpt
    mp2b
    eqtri
end
