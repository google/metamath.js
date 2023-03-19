include "cuhgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "w3a.mm"
include "c0.mm"
include "wne.mm"
include "cvtx.mm"
include "wfn.mm"
include "simp1.mm"
include "wfun.mm"
include "uhgrfun.mm"
include "funfn.mm"
include "sylib.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "uhgrn0.mm"
include "syl3anc.mm"
include "wi.mm"
include "neeq1.mm"
include "biimpd.mm"
include "3ad2ant3.mm"
include "mpd.mm"
include "wss.mm"
include "eqid.mm"
include "uhgrss.mm"
include "3adant3.mm"
include "wb.mm"
include "sseq1.mm"
include "mpbid.mm"
include "cvv.mm"
include "snnzb.mm"
include "snssg.mm"
include "sylbir.mm"
include "syl5ibrcom.mm"

theorem lpvtx
  let cA: class A
  let cG: class G
  let cI: class I
  let cJ: class J
  assume lpvtx.i: |- I = ( iEdg ` G )


  assert |- ( ( G e. UHGraph /\ J e. dom I /\ ( I ` J ) = { A } ) -> A e. ( Vtx ` G ) )

  proof
    cG
    cuhgr
    wcel
    #
    cJ
    cI
    cdm
    #
    wcel
    #
    cJ
    cI
    cfv
    #
    cA
    csn
    #
    wceq
    #
    w3a
    #
    @4
    c0
    wne
    #
    cA
    cG
    cvtx
    cfv
    #
    wcel
    #
    @6
    @3
    c0
    wne
    #
    @7
    @6
    @0
    cI
    @1
    wfn
    #
    @2
    @10
    @0
    @2
    @5
    simp1
    @0
    @2
    @11
    @5
    @0
    cI
    wfun
    @11
    cI
    cG
    lpvtx.i
    uhgrfun
    cI
    funfn
    sylib
    3ad2ant1
    @0
    @2
    @5
    simp2
    @1
    cI
    cJ
    cG
    lpvtx.i
    uhgrn0
    syl3anc
    @5
    @0
    @10
    @7
    wi
    @2
    @5
    @10
    @7
    @3
    @4
    c0
    neeq1
    biimpd
    3ad2ant3
    mpd
    @6
    @9
    @7
    @4
    @8
    wss
    #
    @6
    @3
    @8
    wss
    #
    @12
    @0
    @2
    @13
    @5
    cI
    cJ
    cG
    @8
    @8
    eqid
    lpvtx.i
    uhgrss
    3adant3
    @5
    @0
    @13
    @12
    wb
    @2
    @3
    @4
    @8
    sseq1
    3ad2ant3
    mpbid
    @7
    cA
    cvv
    wcel
    @9
    @12
    wb
    cA
    snnzb
    cA
    @8
    cvv
    snssg
    sylbir
    syl5ibrcom
    mpd
end
