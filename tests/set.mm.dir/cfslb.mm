include "wlim.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "w3a.mm"
include "ccf.mm"
include "cfv.mm"
include "ccrd.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "wa.mm"
include "cv.mm"
include "cpw.mm"
include "crab.mm"
include "ciin.mm"
include "wrex.mm"
include "ssid.mm"
include "wex.mm"
include "ssex.mm"
include "ad2antrr.mm"
include "selpw.mm"
include "sseq1.mm"
include "syl5bb.mm"
include "unieq.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "spcegv.mm"
include "mpcom.mm"
include "df-rex.mm"
include "rabid.mm"
include "anbi1i.mm"
include "exbii.mm"
include "bitri.mm"
include "sylibr.mm"
include "mpan2.mm"
include "iinss.mm"
include "syl.mm"
include "cflim3.mm"
include "syl5ibr.mm"
include "3impib.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "cdm.mm"
include "con0.mm"
include "adantl.mm"
include "word.mm"
include "limord.mm"
include "ordsson.mm"
include "sstr2.mm"
include "mpan9.mm"
include "onssnum.mm"
include "syl2anc.mm"
include "cardid2.mm"
include "3adant3.mm"
include "domentr.mm"

theorem cfslb
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume cfslb.1: |- A e. _V


  assert |- ( ( Lim A /\ B C_ A /\ U. B = A ) -> ( cf ` A ) ~<_ B )

  proof
    cA
    wlim
    #
    cB
    cA
    wss
    #
    cB
    cuni
    #
    cA
    wceq
    #
    w3a
    #
    cA
    ccf
    cfv
    #
    cB
    ccrd
    cfv
    #
    cdom
    wbr
    #
    @6
    cB
    cen
    wbr
    #
    @5
    cB
    cdom
    wbr
    @6
    cvv
    wcel
    @4
    @5
    @6
    wss
    #
    @7
    cB
    ccrd
    fvex
    @0
    @1
    @3
    @9
    @1
    @3
    wa
    #
    @9
    @0
    vx
    vx
    cv
    #
    cuni
    #
    cA
    wceq
    #
    vx
    cA
    cpw
    #
    crab
    #
    @11
    ccrd
    cfv
    #
    ciin
    #
    @6
    wss
    #
    @10
    @16
    @6
    wss
    #
    vx
    @15
    wrex
    #
    @18
    @10
    @6
    @6
    wss
    #
    @20
    @6
    ssid
    @10
    @21
    wa
    #
    @11
    @14
    wcel
    #
    @13
    wa
    #
    @19
    wa
    #
    vx
    wex
    #
    @20
    cB
    cvv
    wcel
    #
    @22
    @26
    @1
    @27
    @3
    @21
    cB
    cA
    cfslb.1
    ssex
    #
    ad2antrr
    @25
    @22
    vx
    cB
    cvv
    @11
    cB
    wceq
    #
    @24
    @10
    @19
    @21
    @29
    @23
    @1
    @13
    @3
    @23
    @11
    cA
    wss
    @29
    @1
    vx
    cA
    selpw
    @11
    cB
    cA
    sseq1
    syl5bb
    @29
    @12
    @2
    cA
    @11
    cB
    unieq
    eqeq1d
    anbi12d
    @29
    @16
    @6
    @6
    @11
    cB
    ccrd
    fveq2
    sseq1d
    anbi12d
    spcegv
    mpcom
    @20
    @11
    @15
    wcel
    #
    @19
    wa
    #
    vx
    wex
    @26
    @19
    vx
    @15
    df-rex
    @31
    @25
    vx
    @30
    @24
    @19
    @13
    vx
    @14
    rabid
    anbi1i
    exbii
    bitri
    sylibr
    mpan2
    vx
    @15
    @16
    @6
    iinss
    syl
    @0
    @5
    @17
    @6
    vx
    cA
    cfslb.1
    cflim3
    sseq1d
    syl5ibr
    3impib
    @5
    @6
    cvv
    ssdomg
    mpsyl
    @0
    @1
    @8
    @3
    @0
    @1
    wa
    #
    cB
    ccrd
    cdm
    wcel
    #
    @8
    @32
    @27
    cB
    con0
    wss
    #
    @33
    @1
    @27
    @0
    @28
    adantl
    @0
    cA
    con0
    wss
    #
    @1
    @34
    @0
    cA
    word
    @35
    cA
    limord
    cA
    ordsson
    syl
    cB
    cA
    con0
    sstr2
    mpan9
    cB
    cvv
    onssnum
    syl2anc
    cB
    cardid2
    syl
    3adant3
    @5
    @6
    cB
    domentr
    syl2anc
end
