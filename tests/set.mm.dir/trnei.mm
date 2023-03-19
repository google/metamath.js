include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "ccl.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "csn.mm"
include "cnei.mm"
include "wral.mm"
include "crest.mm"
include "co.mm"
include "cfil.mm"
include "ctop.mm"
include "cuni.mm"
include "wb.mm"
include "topontop.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "wceq.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "simp3.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "neindisj2.mm"
include "syl3anc.mm"
include "simp1.mm"
include "snssd.mm"
include "snnzg.mm"
include "3ad2ant3.mm"
include "neifil.mm"
include "trfil2.mm"
include "syl2anc.mm"
include "bitr4d.mm"

theorem trnei
  let cA: class A
  let cP: class P
  let cJ: class J
  let cY: class Y
  let vv: setvar v


  assert |- ( ( J e. ( TopOn ` Y ) /\ A C_ Y /\ P e. Y ) -> ( P e. ( ( cls ` J ) ` A ) <-> ( ( ( nei ` J ) ` { P } ) |`t A ) e. ( Fil ` A ) ) )

  proof
    cJ
    cY
    ctopon
    cfv
    wcel
    #
    cA
    cY
    wss
    #
    cP
    cY
    wcel
    #
    w3a
    #
    cP
    cA
    cJ
    ccl
    cfv
    cfv
    wcel
    #
    vv
    cv
    cA
    cin
    c0
    wne
    vv
    cP
    csn
    #
    cJ
    cnei
    cfv
    cfv
    #
    wral
    #
    @6
    cA
    crest
    co
    cA
    cfil
    cfv
    wcel
    #
    @3
    cJ
    ctop
    wcel
    #
    cA
    cJ
    cuni
    #
    wss
    cP
    @10
    wcel
    @4
    @7
    wb
    @0
    @1
    @9
    @2
    cY
    cJ
    topontop
    3ad2ant1
    @3
    cA
    cY
    @10
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    cY
    @10
    wceq
    @2
    cY
    cJ
    toponuni
    3ad2ant1
    #
    sseqtrd
    @3
    cP
    cY
    @10
    @0
    @1
    @2
    simp3
    #
    @12
    eleqtrd
    cP
    cA
    vv
    cJ
    @10
    @10
    eqid
    neindisj2
    syl3anc
    @3
    @6
    cY
    cfil
    cfv
    wcel
    #
    @1
    @8
    @7
    wb
    @3
    @0
    @5
    cY
    wss
    @5
    c0
    wne
    #
    @14
    @0
    @1
    @2
    simp1
    @3
    cP
    cY
    @13
    snssd
    @2
    @0
    @15
    @1
    cP
    cY
    snnzg
    3ad2ant3
    @5
    cJ
    cY
    neifil
    syl3anc
    @11
    vv
    cA
    @6
    cY
    trfil2
    syl2anc
    bitr4d
end
