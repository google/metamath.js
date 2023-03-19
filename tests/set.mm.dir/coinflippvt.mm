include "csn.mm"
include "cfv.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "cdm.mm"
include "cuni.mm"
include "cdif.mm"
include "cprb.mm"
include "wcel.mm"
include "wceq.mm"
include "coinflipprob.mm"
include "cpr.mm"
include "cpw.mm"
include "prid1.mm"
include "snelpwi.mm"
include "ax-mp.mm"
include "coinflipspace.mm"
include "eleqtrri.mm"
include "probdsb.mm"
include "mp2an.mm"
include "coinflipuniv.mm"
include "difeq1i.mm"
include "wne.mm"
include "difprsn1.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "coinflippv.mm"
include "oveq2i.mm"
include "3eqtr3i.mm"
include "1mhlfehlf.mm"

theorem coinflippvt
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


  assert |- ( P ` { T } ) = ( 1 / 2 )

  proof
    cT
    csn
    #
    cP
    cfv
    #
    c1
    c1
    c2
    cdiv
    co
    #
    cmin
    co
    #
    @2
    cP
    cdm
    #
    cuni
    #
    cH
    csn
    #
    cdif
    #
    cP
    cfv
    #
    c1
    @6
    cP
    cfv
    #
    cmin
    co
    #
    @1
    @3
    cP
    cprb
    wcel
    @6
    @4
    wcel
    @8
    @10
    wceq
    cP
    cT
    cH
    cX
    coinflip.h
    coinflip.t
    coinflip.th
    coinflip.2
    coinflip.3
    coinflipprob
    @6
    cH
    cT
    cpr
    #
    cpw
    #
    @4
    cH
    @11
    wcel
    @6
    @12
    wcel
    cH
    cT
    coinflip.h
    prid1
    cH
    @11
    snelpwi
    ax-mp
    cP
    cT
    cH
    cX
    coinflip.h
    coinflip.t
    coinflip.th
    coinflip.2
    coinflip.3
    coinflipspace
    eleqtrri
    @6
    cP
    probdsb
    mp2an
    @7
    @0
    cP
    @7
    @11
    @6
    cdif
    #
    @0
    @5
    @11
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
    coinflipuniv
    difeq1i
    cH
    cT
    wne
    @13
    @0
    wceq
    coinflip.th
    cH
    cT
    difprsn1
    ax-mp
    eqtri
    fveq2i
    @9
    @2
    c1
    cmin
    cP
    cT
    cH
    cX
    coinflip.h
    coinflip.t
    coinflip.th
    coinflip.2
    coinflip.3
    coinflippv
    oveq2i
    3eqtr3i
    1mhlfehlf
    eqtri
end
