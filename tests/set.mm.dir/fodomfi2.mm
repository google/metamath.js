include "wcel.mm"
include "cfn.mm"
include "wfo.mm"
include "w3a.mm"
include "cv.mm"
include "cima.mm"
include "wceq.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "cdom.mm"
include "wbr.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "fofn.mm"
include "3ad2ant3.mm"
include "forn.mm"
include "eqimss2.mm"
include "syl.mm"
include "simp2.mm"
include "fipreima.mm"
include "syl3anc.mm"
include "wa.mm"
include "ccrd.mm"
include "cdm.mm"
include "cres.mm"
include "inss2.mm"
include "sseli.mm"
include "adantl.mm"
include "finnum.mm"
include "wfun.mm"
include "simpl3.mm"
include "fofun.mm"
include "inss1.mm"
include "elpwid.mm"
include "wf.mm"
include "fof.mm"
include "fdm.mm"
include "3syl.mm"
include "sseqtr4d.mm"
include "fores.mm"
include "syl2anc.mm"
include "fodomnum.mm"
include "sylc.mm"
include "simpl1.mm"
include "ssdomg.mm"
include "domtr.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem fodomfi2
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vx: setvar x
  let cX: class X
  let cY: class Y


  assert |- ( ( A e. V /\ B e. Fin /\ F : A -onto-> B ) -> B ~<_ A )

  proof
    cA
    cV
    wcel
    #
    cB
    cfn
    wcel
    #
    cA
    cB
    cF
    wfo
    #
    w3a
    #
    cF
    vx
    cv
    #
    cima
    #
    cB
    wceq
    #
    vx
    cA
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    cB
    cA
    cdom
    wbr
    #
    @3
    cF
    cA
    wfn
    #
    cB
    cF
    crn
    #
    wss
    #
    @1
    @9
    @2
    @0
    @11
    @1
    cA
    cB
    cF
    fofn
    3ad2ant3
    @2
    @0
    @13
    @1
    @2
    @12
    cB
    wceq
    @13
    cA
    cB
    cF
    forn
    cB
    @12
    eqimss2
    syl
    3ad2ant3
    @0
    @1
    @2
    simp2
    cB
    cA
    cF
    vx
    fipreima
    syl3anc
    @3
    @6
    @10
    vx
    @8
    @3
    @4
    @8
    wcel
    #
    wa
    #
    @5
    cA
    cdom
    wbr
    #
    @6
    @10
    @15
    @5
    @4
    cdom
    wbr
    #
    @4
    cA
    cdom
    wbr
    #
    @16
    @15
    @4
    ccrd
    cdm
    wcel
    #
    @4
    @5
    cF
    @4
    cres
    #
    wfo
    #
    @17
    @15
    @4
    cfn
    wcel
    #
    @19
    @14
    @22
    @3
    @8
    cfn
    @4
    @7
    cfn
    inss2
    sseli
    adantl
    @4
    finnum
    syl
    @15
    cF
    wfun
    #
    @4
    cF
    cdm
    #
    wss
    @21
    @15
    @2
    @23
    @0
    @1
    @2
    @14
    simpl3
    #
    cA
    cB
    cF
    fofun
    syl
    @15
    @4
    cA
    @24
    @14
    @4
    cA
    wss
    #
    @3
    @14
    @4
    cA
    @8
    @7
    @4
    @7
    cfn
    inss1
    sseli
    elpwid
    adantl
    #
    @15
    @2
    cA
    cB
    cF
    wf
    @24
    cA
    wceq
    @25
    cA
    cB
    cF
    fof
    cA
    cB
    cF
    fdm
    3syl
    sseqtr4d
    @4
    cF
    fores
    syl2anc
    @4
    @5
    @20
    fodomnum
    sylc
    @15
    @0
    @26
    @18
    @0
    @1
    @2
    @14
    simpl1
    @27
    @4
    cA
    cV
    ssdomg
    sylc
    @5
    @4
    cA
    domtr
    syl2anc
    @5
    cB
    cA
    cdom
    breq1
    syl5ibcom
    rexlimdva
    mpd
end
