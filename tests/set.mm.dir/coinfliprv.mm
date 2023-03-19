include "crrv.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cuni.mm"
include "cr.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cbrsiga.mm"
include "wral.mm"
include "c1.mm"
include "cc0.mm"
include "cpr.mm"
include "wss.mm"
include "cop.mm"
include "wne.mm"
include "1ex.mm"
include "c0ex.mm"
include "fpr.mm"
include "ax-mp.mm"
include "feq1i.mm"
include "mpbir.mm"
include "coinflipuniv.mm"
include "feq2i.mm"
include "wa.mm"
include "1re.mm"
include "0re.mm"
include "pm3.2i.mm"
include "prss.mm"
include "mpbi.mm"
include "fss.mm"
include "mp2an.mm"
include "crn.mm"
include "imassrn.mm"
include "dfdm4.mm"
include "fdmi.mm"
include "eqtr3i.mm"
include "sseqtri.mm"
include "cpw.mm"
include "coinflipspace.mm"
include "eleq2i.mm"
include "cvv.mm"
include "prex.mm"
include "eqeltri.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "mp2b.mm"
include "elpw.mm"
include "bitr2i.mm"
include "biimpi.mm"
include "mp1i.mm"
include "rgen.mm"
include "wb.mm"
include "cprb.mm"
include "coinflipprob.mm"
include "a1i.mm"
include "isrrvv.mm"
include "mpbir2an.mm"

theorem coinfliprv
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


  assert |- X e. ( rRndVar ` P )

  proof
    cX
    cP
    crrv
    cfv
    wcel
    #
    cP
    cdm
    #
    cuni
    #
    cr
    cX
    wf
    #
    cX
    ccnv
    #
    vy
    cv
    #
    cima
    #
    @1
    wcel
    #
    vy
    cbrsiga
    wral
    #
    @2
    c1
    cc0
    cpr
    #
    cX
    wf
    #
    @9
    cr
    wss
    #
    @3
    @10
    cH
    cT
    cpr
    #
    @9
    cX
    wf
    #
    @13
    @12
    @9
    cH
    c1
    cop
    #
    cT
    cc0
    cop
    #
    cpr
    #
    wf
    #
    cH
    cT
    wne
    @17
    coinflip.th
    cH
    cT
    c1
    cc0
    coinflip.h
    coinflip.t
    1ex
    c0ex
    fpr
    ax-mp
    @12
    @9
    cX
    @16
    coinflip.3
    feq1i
    mpbir
    #
    @2
    @12
    @9
    cX
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
    feq2i
    mpbir
    c1
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    wa
    @11
    @19
    @20
    1re
    0re
    pm3.2i
    c1
    cc0
    cr
    1ex
    c0ex
    prss
    mpbi
    @2
    @9
    cr
    cX
    fss
    mp2an
    @7
    vy
    cbrsiga
    @6
    @12
    wss
    #
    @7
    @5
    cbrsiga
    wcel
    @6
    @4
    crn
    #
    @12
    @4
    @5
    imassrn
    cX
    cdm
    @22
    @12
    cX
    dfdm4
    @12
    @9
    cX
    @18
    fdmi
    eqtr3i
    sseqtri
    @21
    @7
    @7
    @6
    @12
    cpw
    #
    wcel
    @21
    @1
    @23
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
    coinflipspace
    eleq2i
    @6
    @12
    cX
    cvv
    wcel
    @4
    cvv
    wcel
    @6
    cvv
    wcel
    cX
    @16
    cvv
    coinflip.3
    @14
    @15
    prex
    eqeltri
    cX
    cvv
    cnvexg
    @4
    @5
    cvv
    imaexg
    mp2b
    elpw
    bitr2i
    biimpi
    mp1i
    rgen
    cH
    cvv
    wcel
    #
    @0
    @3
    @8
    wa
    wb
    coinflip.h
    @24
    vy
    cP
    cX
    cP
    cprb
    wcel
    @24
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
    a1i
    isrrvv
    ax-mp
    mpbir2an
end
