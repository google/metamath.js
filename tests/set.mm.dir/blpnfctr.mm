include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cpnf.mm"
include "cbl.mm"
include "co.mm"
include "w3a.mm"
include "ccnv.mm"
include "cr.mm"
include "cima.mm"
include "cec.mm"
include "wer.mm"
include "eqid.mm"
include "xmeter.mm"
include "3ad2ant1.mm"
include "wbr.mm"
include "simp3.mm"
include "wceq.mm"
include "xmetec.mm"
include "3adant3.mm"
include "eleqtrrd.mm"
include "wb.mm"
include "elecg.mm"
include "ancoms.mm"
include "3adant1.mm"
include "mpbid.mm"
include "erthi.mm"
include "wa.mm"
include "cxr.mm"
include "wss.mm"
include "pnfxr.mm"
include "blssm.mm"
include "mp3an3.mm"
include "sselda.mm"
include "adantlr.mm"
include "syldan.mm"
include "3impa.mm"
include "3eqtr3d.mm"

theorem blpnfctr
  let cA: class A
  let cD: class D
  let cP: class P
  let cX: class X


  assert |- ( ( D e. ( *Met ` X ) /\ P e. X /\ A e. ( P ( ball ` D ) +oo ) ) -> ( P ( ball ` D ) +oo ) = ( A ( ball ` D ) +oo ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    cA
    cP
    cpnf
    cD
    cbl
    cfv
    #
    co
    #
    wcel
    #
    w3a
    #
    cP
    cD
    ccnv
    cr
    cima
    #
    cec
    #
    cA
    @6
    cec
    #
    @3
    cA
    cpnf
    @2
    co
    #
    @5
    cP
    cA
    @6
    cX
    @0
    @1
    cX
    @6
    wer
    @4
    cD
    @6
    cX
    @6
    eqid
    #
    xmeter
    3ad2ant1
    @5
    cA
    @7
    wcel
    #
    cP
    cA
    @6
    wbr
    #
    @5
    cA
    @3
    @7
    @0
    @1
    @4
    simp3
    @0
    @1
    @7
    @3
    wceq
    @4
    cD
    cP
    @6
    cX
    @10
    xmetec
    3adant3
    #
    eleqtrrd
    @1
    @4
    @11
    @12
    wb
    #
    @0
    @4
    @1
    @14
    cA
    cP
    @6
    @3
    cX
    elecg
    ancoms
    3adant1
    mpbid
    erthi
    @13
    @0
    @1
    @4
    @8
    @9
    wceq
    #
    @0
    @1
    wa
    #
    @4
    cA
    cX
    wcel
    #
    @15
    @16
    @3
    cX
    cA
    @0
    @1
    cpnf
    cxr
    wcel
    @3
    cX
    wss
    pnfxr
    cD
    cP
    cpnf
    cX
    blssm
    mp3an3
    sselda
    @0
    @17
    @15
    @1
    cD
    cA
    @6
    cX
    @10
    xmetec
    adantlr
    syldan
    3impa
    3eqtr3d
end
