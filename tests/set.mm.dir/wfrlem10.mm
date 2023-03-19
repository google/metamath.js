include "cdm.mm"
include "cdif.mm"
include "cv.mm"
include "cpred.mm"
include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "wfrlem8.mm"
include "biimpi.mm"
include "wss.mm"
include "predss.mm"
include "a1i.mm"
include "wa.mm"
include "wbr.mm"
include "simpr.mm"
include "weq.mm"
include "wn.mm"
include "eldifn.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "con2d.mm"
include "imp.mm"
include "wfrdmcl.mm"
include "adantl.mm"
include "wi.mm"
include "ssel.mm"
include "con3d.mm"
include "syl5com.mm"
include "adantr.mm"
include "mpd.mm"
include "wb.mm"
include "eldifi.mm"
include "elpredg.mm"
include "ancoms.mm"
include "sylan.mm"
include "mtbid.mm"
include "w3o.mm"
include "wfrdmss.mm"
include "sseli.mm"
include "wor.mm"
include "wwe.mm"
include "weso.mm"
include "ax-mp.mm"
include "solin.mm"
include "mpan.mm"
include "syl2anr.mm"
include "ecase23d.mm"
include "cvv.mm"
include "vex.mm"
include "elpred.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "sylan9eqr.mm"

theorem wfrlem10
  let vz: setvar z
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G
  let vw: setvar w
  assume wfrlem10.1: |- R We A
  assume wfrlem10.2: |- F = wrecs ( R , A , G )

  disjoint A z
  disjoint A w
  disjoint w z
  disjoint F w
  disjoint R w
  assert |- ( ( z e. ( A \ dom F ) /\ Pred ( R , ( A \ dom F ) , z ) = (/) ) -> Pred ( R , A , z ) = dom F )

  proof
    cA
    cF
    cdm
    #
    cdif
    #
    cR
    vz
    cv
    #
    cpred
    c0
    wceq
    #
    @2
    @1
    wcel
    #
    cA
    cR
    @2
    cpred
    #
    @0
    cR
    @2
    cpred
    #
    @0
    @3
    @5
    @6
    wceq
    cA
    cR
    cF
    cG
    @2
    wfrlem10.2
    wfrlem8
    biimpi
    @4
    @6
    @0
    @6
    @0
    wss
    @4
    @0
    cR
    @2
    predss
    a1i
    @4
    vw
    @0
    @6
    @4
    vw
    cv
    #
    @0
    wcel
    #
    @7
    @6
    wcel
    #
    @4
    @8
    wa
    #
    @8
    @7
    @2
    cR
    wbr
    #
    @9
    @4
    @8
    simpr
    @10
    @11
    vw
    vz
    weq
    #
    @2
    @7
    cR
    wbr
    #
    @4
    @8
    @12
    wn
    @4
    @12
    @8
    @4
    @8
    wn
    @12
    @2
    @0
    wcel
    #
    wn
    #
    @2
    cA
    @0
    eldifn
    #
    @12
    @8
    @14
    @7
    @2
    @0
    eleq1
    notbid
    syl5ibrcom
    con2d
    imp
    @10
    @2
    cA
    cR
    @7
    cpred
    #
    wcel
    #
    @13
    @10
    @17
    @0
    wss
    #
    @18
    wn
    #
    @8
    @19
    @4
    cA
    cR
    cF
    cG
    @7
    wfrlem10.2
    wfrdmcl
    adantl
    @4
    @19
    @20
    wi
    @8
    @4
    @15
    @19
    @20
    @16
    @19
    @18
    @14
    @17
    @0
    @2
    ssel
    con3d
    syl5com
    adantr
    mpd
    @4
    @2
    cA
    wcel
    #
    @8
    @18
    @13
    wb
    #
    @2
    cA
    @0
    eldifi
    #
    @8
    @21
    @22
    cA
    @0
    cR
    @7
    @2
    elpredg
    ancoms
    sylan
    mtbid
    @8
    @7
    cA
    wcel
    #
    @21
    @11
    @12
    @13
    w3o
    #
    @4
    @0
    cA
    @7
    cA
    cR
    cF
    cG
    wfrlem10.2
    wfrdmss
    sseli
    @23
    cA
    cR
    wor
    #
    @24
    @21
    wa
    @25
    cA
    cR
    wwe
    @26
    wfrlem10.1
    cA
    cR
    weso
    ax-mp
    cA
    @7
    @2
    cR
    solin
    mpan
    syl2anr
    ecase23d
    @2
    cvv
    wcel
    @9
    @8
    @11
    wa
    wb
    vz
    vex
    @0
    cvv
    cR
    @2
    @7
    vw
    vex
    elpred
    ax-mp
    sylanbrc
    ex
    ssrdv
    eqssd
    sylan9eqr
end
