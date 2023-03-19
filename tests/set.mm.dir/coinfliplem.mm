include "chash.mm"
include "cpr.mm"
include "cpw.mm"
include "cres.mm"
include "c2.mm"
include "cdiv.mm"
include "cofc.mm"
include "co.mm"
include "cxdiv.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cr.mm"
include "cfn.mm"
include "cv.mm"
include "wa.mm"
include "cfv.mm"
include "simpr.mm"
include "fvres.mm"
include "syl.mm"
include "cn0.mm"
include "wss.mm"
include "prfi.mm"
include "elpwid.mm"
include "ssfi.mm"
include "sylancr.mm"
include "hashcl.mm"
include "nn0red.mm"
include "eqeltrd.mm"
include "cc0.mm"
include "wne.mm"
include "2re.mm"
include "a1i.mm"
include "2ne0.mm"
include "rexdiv.mm"
include "syl3anc.mm"
include "wfn.mm"
include "hashresfn.mm"
include "pwfi.mm"
include "mpbi.mm"
include "ofcfeqd2.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem coinfliplem
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


  assert |- P = ( ( # |` ~P { H , T } ) oFC /e 2 )

  proof
    cP
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
    @2
    c2
    cxdiv
    cofc
    co
    #
    coinflip.2
    cH
    cvv
    wcel
    #
    @4
    @3
    wceq
    coinflip.h
    @5
    vx
    vy
    @1
    cr
    c2
    cdiv
    cxdiv
    @2
    cfn
    cr
    @5
    vx
    cv
    #
    @1
    wcel
    #
    wa
    #
    @6
    @2
    cfv
    #
    @6
    chash
    cfv
    #
    cr
    @8
    @7
    @9
    @10
    wceq
    @5
    @7
    simpr
    #
    @6
    @1
    chash
    fvres
    syl
    @8
    @10
    @8
    @6
    cfn
    wcel
    #
    @10
    cn0
    wcel
    @8
    @0
    cfn
    wcel
    #
    @6
    @0
    wss
    @12
    cH
    cT
    prfi
    #
    @8
    @6
    @0
    @11
    elpwid
    @0
    @6
    ssfi
    sylancr
    @6
    hashcl
    syl
    nn0red
    eqeltrd
    @5
    vy
    cv
    #
    cr
    wcel
    #
    wa
    #
    @16
    c2
    cr
    wcel
    #
    c2
    cc0
    wne
    #
    @15
    c2
    cxdiv
    co
    @15
    c2
    cdiv
    co
    wceq
    @5
    @16
    simpr
    @18
    @17
    2re
    a1i
    @19
    @17
    2ne0
    a1i
    @15
    c2
    rexdiv
    syl3anc
    @2
    @1
    wfn
    @5
    @1
    hashresfn
    a1i
    @1
    cfn
    wcel
    #
    @5
    @13
    @20
    @14
    @0
    pwfi
    mpbi
    a1i
    @18
    @5
    2re
    a1i
    ofcfeqd2
    ax-mp
    eqtr4i
end
