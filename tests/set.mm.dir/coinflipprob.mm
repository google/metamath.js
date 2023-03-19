include "chash.mm"
include "cpr.mm"
include "cpw.mm"
include "cres.mm"
include "cuni.mm"
include "cfv.mm"
include "cxdiv.mm"
include "cofc.mm"
include "co.mm"
include "cprb.mm"
include "c2.mm"
include "coinfliplem.mm"
include "wcel.mm"
include "wceq.mm"
include "unipw.mm"
include "prex.mm"
include "pwid.mm"
include "eqeltri.mm"
include "fvres.mm"
include "ax-mp.mm"
include "fveq2i.mm"
include "wne.mm"
include "cvv.mm"
include "wb.mm"
include "hashprg.mm"
include "mp2an.mm"
include "mpbi.mm"
include "3eqtri.mm"
include "oveq2i.mm"
include "eqtr4i.mm"
include "cmeas.mm"
include "crp.mm"
include "pwcntmeas.mm"
include "2rp.mm"
include "probfinmeasb.mm"

theorem coinflipprob
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


  assert |- P e. Prob

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
    @1
    cuni
    #
    @2
    cfv
    #
    cxdiv
    cofc
    #
    co
    #
    cprb
    cP
    @2
    c2
    @5
    co
    @6
    cP
    cT
    cH
    cX
    coinflip.h
    coinflip.t
    coinflip.th
    coinflip.2
    coinflip.3
    coinfliplem
    @4
    c2
    @2
    @5
    @4
    @3
    chash
    cfv
    #
    @0
    chash
    cfv
    #
    c2
    @3
    @1
    wcel
    @4
    @7
    wceq
    @3
    @0
    @1
    @0
    unipw
    #
    @0
    cH
    cT
    prex
    #
    pwid
    eqeltri
    @3
    @1
    chash
    fvres
    ax-mp
    @3
    @0
    chash
    @9
    fveq2i
    cH
    cT
    wne
    #
    @8
    c2
    wceq
    #
    coinflip.th
    cH
    cvv
    wcel
    cT
    cvv
    wcel
    @11
    @12
    wb
    coinflip.h
    coinflip.t
    cH
    cT
    cvv
    cvv
    hashprg
    mp2an
    mpbi
    3eqtri
    #
    oveq2i
    eqtr4i
    @2
    @1
    cmeas
    cfv
    wcel
    #
    @4
    crp
    wcel
    @6
    cprb
    wcel
    @0
    cvv
    wcel
    @14
    @10
    @0
    cvv
    pwcntmeas
    ax-mp
    @4
    c2
    crp
    @13
    2rp
    eqeltri
    @1
    @2
    probfinmeasb
    mp2an
    eqeltri
end
