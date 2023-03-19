include "cr.mm"
include "wcel.mm"
include "cxr.mm"
include "wa.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "cima.mm"
include "cec.mm"
include "wss.mm"
include "rexr.mm"
include "cxmt.mm"
include "xrsxmet.mm"
include "eqid.mm"
include "blssec.mm"
include "mp3an1.mm"
include "sylan.mm"
include "cv.mm"
include "wbr.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "simpl.mm"
include "elecg.mm"
include "sylancr.mm"
include "w3a.mm"
include "xmeterval.mm"
include "ax-mp.mm"
include "wceq.mm"
include "simpr.mm"
include "simplll.mm"
include "eqeltrrd.mm"
include "wne.mm"
include "simplr3.mm"
include "simplr1.mm"
include "simplr2.mm"
include "xrsdsreclb.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "simprd.mm"
include "pm2.61dane.mm"
include "ex.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "sstrd.mm"

theorem xrsblre
  let cD: class D
  let cP: class P
  let cR: class R
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  assume xrsxmet.1: |- D = ( dist ` RR*s )


  assert |- ( ( P e. RR /\ R e. RR* ) -> ( P ( ball ` D ) R ) C_ RR )

  proof
    cP
    cr
    wcel
    #
    cR
    cxr
    wcel
    #
    wa
    #
    cP
    cR
    cD
    cbl
    cfv
    co
    #
    cP
    cD
    ccnv
    cr
    cima
    #
    cec
    #
    cr
    @0
    cP
    cxr
    wcel
    #
    @1
    @3
    @5
    wss
    #
    cP
    rexr
    cD
    cxr
    cxmt
    cfv
    wcel
    #
    @6
    @1
    @7
    cD
    xrsxmet.1
    xrsxmet
    #
    cD
    cP
    @4
    cR
    cxr
    @4
    eqid
    #
    blssec
    mp3an1
    sylan
    @2
    vx
    @5
    cr
    @2
    vx
    cv
    #
    @5
    wcel
    #
    cP
    @11
    @4
    wbr
    #
    @11
    cr
    wcel
    #
    @2
    @11
    cvv
    wcel
    @0
    @12
    @13
    wb
    vx
    vex
    @0
    @1
    simpl
    @11
    cP
    @4
    cvv
    cr
    elecg
    sylancr
    @13
    @6
    @11
    cxr
    wcel
    #
    cP
    @11
    cD
    co
    cr
    wcel
    #
    w3a
    #
    @2
    @14
    @8
    @13
    @17
    wb
    @9
    cP
    @11
    cD
    @4
    cxr
    @10
    xmeterval
    ax-mp
    @2
    @17
    @14
    @2
    @17
    wa
    #
    @14
    cP
    @11
    @18
    cP
    @11
    wceq
    #
    wa
    cP
    @11
    cr
    @18
    @19
    simpr
    @0
    @1
    @17
    @19
    simplll
    eqeltrrd
    @18
    cP
    @11
    wne
    #
    wa
    #
    @0
    @14
    @21
    @16
    @0
    @14
    wa
    #
    @6
    @15
    @16
    @2
    @20
    simplr3
    @21
    @6
    @15
    @20
    @16
    @22
    wb
    @6
    @15
    @16
    @2
    @20
    simplr1
    @6
    @15
    @16
    @2
    @20
    simplr2
    @18
    @20
    simpr
    cP
    @11
    cD
    xrsxmet.1
    xrsdsreclb
    syl3anc
    mpbid
    simprd
    pm2.61dane
    ex
    syl5bi
    sylbid
    ssrdv
    sstrd
end
