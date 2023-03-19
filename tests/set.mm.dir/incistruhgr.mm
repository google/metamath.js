include "wcel.mm"
include "cxp.mm"
include "wss.mm"
include "crn.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cmpt.mm"
include "wa.mm"
include "cuhgr.mm"
include "cdm.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "id.mm"
include "rabeqdv.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "xpeq1.mm"
include "sseq2d.mm"
include "3anbi2d.mm"
include "anbi12d.mm"
include "wi.mm"
include "dmeq.mm"
include "cvtx.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "eqid.mm"
include "dmmpti.mm"
include "a1i.mm"
include "eqtrd.mm"
include "ssrab2.mm"
include "elpw.mm"
include "sylibr.mm"
include "wrex.mm"
include "wn.mm"
include "wb.mm"
include "eleq2.mm"
include "3ad2ant3.mm"
include "ssrelrn.mm"
include "ex.mm"
include "3ad2ant2.mm"
include "sylbird.mm"
include "imp.mm"
include "wne.mm"
include "df-ne.mm"
include "rabn0.mm"
include "bitr3i.mm"
include "elsn.mm"
include "sylnibr.mm"
include "eldifd.mm"
include "fmptd.mm"
include "simpl.mm"
include "simpr.mm"
include "feq12d.mm"
include "syl5ibr.mm"
include "mpdan.mm"
include "syl6bir.mm"
include "expdimp.mm"
include "impcom.mm"
include "isuhgr.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "mpbird.mm"

theorem incistruhgr
  let vv: setvar v
  let cP: class P
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cI: class I
  let cL: class L
  let cV: class V
  let cW: class W
  assume incistruhgr.v: |- V = ( Vtx ` G )
  assume incistruhgr.e: |- E = ( iEdg ` G )

  disjoint E e
  disjoint G e
  disjoint I e
  disjoint I v
  disjoint e v
  disjoint L e
  disjoint L v
  disjoint P e
  disjoint P v
  disjoint V e
  disjoint V v
  disjoint W e
  assert |- ( ( G e. W /\ I C_ ( P X. L ) /\ ran I = L ) -> ( ( V = P /\ E = ( e e. L |-> { v e. P | v I e } ) ) -> G e. UHGraph ) )

  proof
    cG
    cW
    wcel
    #
    cI
    cP
    cL
    cxp
    #
    wss
    #
    cI
    crn
    #
    cL
    wceq
    #
    w3a
    #
    cV
    cP
    wceq
    #
    cE
    ve
    cL
    vv
    cv
    ve
    cv
    #
    cI
    wbr
    #
    vv
    cP
    crab
    #
    cmpt
    #
    wceq
    #
    wa
    #
    cG
    cuhgr
    wcel
    #
    @5
    @12
    wa
    @13
    cE
    cdm
    #
    cV
    cpw
    #
    c0
    csn
    #
    cdif
    #
    cE
    wf
    #
    @12
    @5
    @18
    @6
    @11
    @5
    @18
    @6
    @11
    @5
    wa
    cE
    ve
    cL
    @8
    vv
    cV
    crab
    #
    cmpt
    #
    wceq
    #
    @0
    cI
    cV
    cL
    cxp
    #
    wss
    #
    @4
    w3a
    #
    wa
    @18
    @6
    @21
    @11
    @24
    @5
    @6
    @20
    @10
    cE
    @6
    ve
    cL
    @19
    @9
    @6
    @8
    vv
    cV
    cP
    @6
    id
    rabeqdv
    mpteq2dv
    eqeq2d
    @6
    @23
    @2
    @0
    @4
    @6
    @22
    @1
    cI
    cV
    cP
    cL
    xpeq1
    sseq2d
    3anbi2d
    anbi12d
    @21
    @24
    @18
    @21
    @14
    cL
    wceq
    #
    @24
    @18
    wi
    @21
    @14
    @20
    cdm
    #
    cL
    cE
    @20
    dmeq
    @26
    cL
    wceq
    @21
    ve
    cL
    @19
    @20
    @8
    vv
    cV
    cV
    cG
    cvtx
    cfv
    cvv
    incistruhgr.v
    cG
    cvtx
    fvex
    eqeltri
    rabex
    #
    @20
    eqid
    #
    dmmpti
    a1i
    eqtrd
    @24
    @18
    @21
    @25
    wa
    #
    cL
    @17
    @20
    wf
    @24
    ve
    cL
    @19
    @17
    @20
    @24
    @7
    cL
    wcel
    #
    wa
    #
    @19
    @15
    @16
    @31
    @19
    cV
    wss
    #
    @19
    @15
    wcel
    @32
    @31
    @8
    vv
    cV
    ssrab2
    a1i
    @19
    cV
    @27
    elpw
    sylibr
    @31
    @19
    c0
    wceq
    #
    @19
    @16
    wcel
    @31
    @8
    vv
    cV
    wrex
    #
    @33
    wn
    #
    @24
    @30
    @34
    @24
    @30
    @7
    @3
    wcel
    #
    @34
    @4
    @0
    @36
    @30
    wb
    @23
    @3
    cL
    @7
    eleq2
    3ad2ant3
    @23
    @0
    @36
    @34
    wi
    @4
    @23
    @36
    @34
    cV
    cL
    cI
    @7
    vv
    ssrelrn
    ex
    3ad2ant2
    sylbird
    imp
    @35
    @19
    c0
    wne
    @34
    @19
    c0
    df-ne
    @8
    vv
    cV
    rabn0
    bitr3i
    sylibr
    @19
    c0
    @27
    elsn
    sylnibr
    eldifd
    @28
    fmptd
    @29
    @14
    cL
    @17
    cE
    @20
    @21
    @25
    simpl
    @21
    @25
    simpr
    feq12d
    syl5ibr
    mpdan
    imp
    syl6bir
    expdimp
    impcom
    @5
    @13
    @18
    wb
    #
    @12
    @0
    @2
    @37
    @4
    cW
    cE
    cG
    cV
    incistruhgr.v
    incistruhgr.e
    isuhgr
    3ad2ant1
    adantr
    mpbird
    ex
end
