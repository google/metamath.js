include "cle.mm"
include "ccnv.mm"
include "cxp.mm"
include "cin.mm"
include "cordt.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "wceq.mm"
include "wtru.mm"
include "cxr.mm"
include "crn.mm"
include "cdm.mm"
include "lern.mm"
include "df-rn.mm"
include "eqtri.mm"
include "ctsr.mm"
include "wcel.mm"
include "letsr.mm"
include "cnvtsr.mm"
include "ax-mp.mm"
include "a1i.mm"
include "wss.mm"
include "cv.mm"
include "wa.mm"
include "wbr.mm"
include "crab.mm"
include "wb.mm"
include "brcnvg.mm"
include "adantlr.mm"
include "simpr.mm"
include "simplr.mm"
include "syl2anc.mm"
include "anbi12d.mm"
include "ancom.mm"
include "syl6bb.mm"
include "rabbidva.mm"
include "cicc.mm"
include "sseldi.mm"
include "simpl.mm"
include "iccval.mm"
include "ancoms.mm"
include "eqsstr3d.mm"
include "eqsstrd.mm"
include "adantl.mm"
include "ordtrest2.mm"
include "trud.mm"
include "cps.mm"
include "tsrps.mm"
include "ordtcnv.mm"
include "oveq1i.mm"
include "eqtr2i.mm"

theorem cnvordtrestixx
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume cnvordtrestixx.1: |- A C_ RR*
  assume cnvordtrestixx.2: |- ( ( x e. A /\ y e. A ) -> ( x [,] y ) C_ A )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( ( ordTop ` <_ ) |`t A ) = ( ordTop ` ( `' <_ i^i ( A X. A ) ) )

  proof
    cle
    ccnv
    #
    cA
    cA
    cxp
    cin
    cordt
    cfv
    #
    @0
    cordt
    cfv
    #
    cA
    crest
    co
    #
    cle
    cordt
    cfv
    #
    cA
    crest
    co
    @1
    @3
    wceq
    wtru
    vy
    vx
    vz
    cA
    @0
    cxr
    cxr
    cle
    crn
    @0
    cdm
    lern
    cle
    df-rn
    eqtri
    @0
    ctsr
    wcel
    #
    wtru
    cle
    ctsr
    wcel
    #
    @5
    letsr
    cle
    cnvtsr
    ax-mp
    a1i
    cA
    cxr
    wss
    wtru
    cnvordtrestixx.1
    a1i
    vy
    cv
    #
    cA
    wcel
    #
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    @7
    vz
    cv
    #
    @0
    wbr
    #
    @12
    @9
    @0
    wbr
    #
    wa
    #
    vz
    cxr
    crab
    #
    cA
    wss
    wtru
    @11
    @16
    @9
    @12
    cle
    wbr
    #
    @12
    @7
    cle
    wbr
    #
    wa
    #
    vz
    cxr
    crab
    #
    cA
    @11
    @15
    @19
    vz
    cxr
    @11
    @12
    cxr
    wcel
    #
    wa
    #
    @15
    @18
    @17
    wa
    @19
    @22
    @13
    @18
    @14
    @17
    @8
    @21
    @13
    @18
    wb
    @10
    @7
    @12
    cA
    cxr
    cle
    brcnvg
    adantlr
    @22
    @21
    @10
    @14
    @17
    wb
    @11
    @21
    simpr
    @8
    @10
    @21
    simplr
    @12
    @9
    cxr
    cA
    cle
    brcnvg
    syl2anc
    anbi12d
    @18
    @17
    ancom
    syl6bb
    rabbidva
    @11
    @20
    @9
    @7
    cicc
    co
    #
    cA
    @11
    @9
    cxr
    wcel
    @7
    cxr
    wcel
    @23
    @20
    wceq
    @11
    cA
    cxr
    @9
    cnvordtrestixx.1
    @8
    @10
    simpr
    sseldi
    @11
    cA
    cxr
    @7
    cnvordtrestixx.1
    @8
    @10
    simpl
    sseldi
    vz
    @9
    @7
    iccval
    syl2anc
    @10
    @8
    @23
    cA
    wss
    cnvordtrestixx.2
    ancoms
    eqsstr3d
    eqsstrd
    adantl
    ordtrest2
    trud
    @2
    @4
    cA
    crest
    cle
    cps
    wcel
    #
    @2
    @4
    wceq
    @6
    @24
    letsr
    cle
    tsrps
    ax-mp
    cle
    ordtcnv
    ax-mp
    oveq1i
    eqtr2i
end
