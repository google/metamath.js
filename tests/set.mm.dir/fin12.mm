include "cfn.mm"
include "wcel.mm"
include "cfin2.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "crpss.mm"
include "wor.mm"
include "wa.mm"
include "cuni.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "wpss.mm"
include "wn.mm"
include "wrex.mm"
include "ccnv.mm"
include "wbr.mm"
include "cvv.mm"
include "wfr.mm"
include "wss.mm"
include "vex.mm"
include "a1i.mm"
include "isfin1-3.mm"
include "ibi.mm"
include "ad2antrr.mm"
include "elpwi.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "fri.mm"
include "syl22anc.mm"
include "brcnv.mm"
include "brrpss.mm"
include "bitri.mm"
include "notbii.mm"
include "ralbii.mm"
include "rexbii.mm"
include "sylib.mm"
include "wb.mm"
include "sorpssuni.mm"
include "ad2antll.mm"
include "mpbid.mm"
include "ex.mm"
include "ralrimiva.mm"
include "isfin2.mm"
include "mpbird.mm"

theorem fin12
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cV: class V
  let cX: class X
  let cC: class C


  assert |- ( A e. Fin -> A e. Fin2 )

  proof
    cA
    cfn
    wcel
    #
    cA
    cfin2
    wcel
    vb
    cv
    #
    c0
    wne
    #
    @1
    crpss
    wor
    #
    wa
    #
    @1
    cuni
    @1
    wcel
    #
    wi
    #
    vb
    cA
    cpw
    #
    cpw
    #
    wral
    @0
    @6
    vb
    @8
    @0
    @1
    @8
    wcel
    #
    wa
    #
    @4
    @5
    @10
    @4
    wa
    #
    vc
    cv
    #
    vd
    cv
    #
    wpss
    #
    wn
    #
    vd
    @1
    wral
    #
    vc
    @1
    wrex
    #
    @5
    @11
    @13
    @12
    crpss
    ccnv
    #
    wbr
    #
    wn
    #
    vd
    @1
    wral
    #
    vc
    @1
    wrex
    #
    @17
    @11
    @1
    cvv
    wcel
    #
    @7
    @18
    wfr
    #
    @1
    @7
    wss
    #
    @2
    @22
    @23
    @11
    vb
    vex
    a1i
    @0
    @24
    @9
    @4
    @0
    @24
    cA
    cfn
    isfin1-3
    ibi
    ad2antrr
    @9
    @25
    @0
    @4
    @1
    @7
    elpwi
    ad2antlr
    @10
    @2
    @3
    simprl
    vc
    vd
    @7
    @1
    cvv
    @18
    fri
    syl22anc
    @21
    @16
    vc
    @1
    @20
    @15
    vd
    @1
    @19
    @14
    @19
    @12
    @13
    crpss
    wbr
    @14
    @13
    @12
    crpss
    vd
    vex
    #
    vc
    vex
    brcnv
    @12
    @13
    @26
    brrpss
    bitri
    notbii
    ralbii
    rexbii
    sylib
    @3
    @17
    @5
    wb
    @10
    @2
    vd
    vc
    @1
    sorpssuni
    ad2antll
    mpbid
    ex
    ralrimiva
    vb
    cA
    cfn
    isfin2
    mpbird
end
