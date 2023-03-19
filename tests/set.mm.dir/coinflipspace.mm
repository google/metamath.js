include "cdm.mm"
include "chash.mm"
include "cpr.mm"
include "cpw.mm"
include "cres.mm"
include "c2.mm"
include "cdiv.mm"
include "cofc.mm"
include "co.mm"
include "dmeqi.mm"
include "cvv.mm"
include "wcel.mm"
include "wfn.mm"
include "wceq.mm"
include "cr.mm"
include "hashresfn.mm"
include "a1i.mm"
include "prex.mm"
include "pwexg.mm"
include "mp1i.mm"
include "2re.mm"
include "ofcfn.mm"
include "fndm.mm"
include "mp2b.mm"
include "eqtri.mm"

theorem coinflipspace
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


  assert |- dom P = ~P { H , T }

  proof
    cP
    cdm
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
    cdm
    #
    @1
    cP
    @3
    coinflip.2
    dmeqi
    cH
    cvv
    wcel
    #
    @3
    @1
    wfn
    @4
    @1
    wceq
    coinflip.h
    @5
    @1
    c2
    cdiv
    @2
    cvv
    cr
    @2
    @1
    wfn
    @5
    @1
    hashresfn
    a1i
    @0
    cvv
    wcel
    @1
    cvv
    wcel
    @5
    cH
    cT
    prex
    @0
    cvv
    pwexg
    mp1i
    c2
    cr
    wcel
    @5
    2re
    a1i
    ofcfn
    @1
    @3
    fndm
    mp2b
    eqtri
end
