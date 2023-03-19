include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "c0.mm"
include "noel.mm"
include "crn.mm"
include "cpmtr.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "rn0.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "mtbiri.mm"
include "con4i.mm"
include "cv.mm"
include "cpw.mm"
include "wrex.mm"
include "crab.mm"
include "wfn.mm"
include "wb.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "cif.mm"
include "cmpt.mm"
include "wral.mm"
include "mptexg.mm"
include "ralrimivw.mm"
include "eqid.mm"
include "fnmpt.mm"
include "syl.mm"
include "pmtrfval.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "fvelrnb.mm"
include "eleq2i.mm"
include "breq1.mm"
include "rexrab.mm"
include "bicomi.mm"
include "3bitr4g.mm"
include "wi.mm"
include "elpwi.mm"
include "cid.mm"
include "cdm.mm"
include "simp1.mm"
include "pmtrmvd.mm"
include "simp2.mm"
include "eqsstrd.mm"
include "simp3.mm"
include "eqbrtrd.mm"
include "3jca.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "jca.mm"
include "difeq1.mm"
include "dmeqd.mm"
include "syl6eqr.mm"
include "sseq1.mm"
include "3anbi23d.mm"
include "adantl.mm"
include "simpl.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "mpdan.mm"
include "syl5ibcom.mm"
include "3exp.mm"
include "imp4a.mm"
include "syl5.mm"
include "rexlimdv.mm"
include "sylbid.mm"
include "mpcom.mm"

theorem pmtrfrn
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cV: class V
  assume pmtrrn.t: |- T = ( pmTrsp ` D )
  assume pmtrrn.r: |- R = ran T
  assume pmtrfrn.p: |- P = dom ( F \ _I )


  assert |- ( F e. R -> ( ( D e. _V /\ P C_ D /\ P ~~ 2o ) /\ F = ( T ` P ) ) )

  proof
    cD
    cvv
    wcel
    #
    cF
    cR
    wcel
    #
    @0
    cP
    cD
    wss
    #
    cP
    c2o
    cen
    wbr
    #
    w3a
    #
    cF
    cP
    cT
    cfv
    #
    wceq
    #
    wa
    #
    @0
    @1
    @0
    wn
    #
    @1
    cF
    c0
    wcel
    cF
    noel
    @8
    cR
    c0
    cF
    @8
    cR
    cT
    crn
    #
    c0
    pmtrrn.r
    @8
    @9
    c0
    crn
    c0
    @8
    cT
    c0
    @8
    cT
    cD
    cpmtr
    cfv
    c0
    pmtrrn.t
    cD
    cpmtr
    fvprc
    syl5eq
    rneqd
    rn0
    syl6eq
    syl5eq
    eleq2d
    mtbiri
    con4i
    @0
    @1
    vy
    cv
    #
    c2o
    cen
    wbr
    #
    @10
    cT
    cfv
    #
    cF
    wceq
    #
    wa
    #
    vy
    cD
    cpw
    #
    wrex
    #
    @7
    @0
    cF
    @9
    wcel
    #
    @13
    vy
    vx
    cv
    #
    c2o
    cen
    wbr
    #
    vx
    @15
    crab
    #
    wrex
    #
    @1
    @16
    @0
    cT
    @20
    wfn
    #
    @17
    @21
    wb
    @0
    @22
    vw
    @20
    vz
    cD
    vz
    cv
    #
    vw
    cv
    #
    wcel
    @24
    @23
    csn
    cdif
    cuni
    @23
    cif
    #
    cmpt
    #
    cmpt
    #
    @20
    wfn
    #
    @0
    @26
    cvv
    wcel
    #
    vw
    @20
    wral
    @28
    @0
    @29
    vw
    @20
    vz
    cD
    @25
    cvv
    mptexg
    ralrimivw
    vw
    @20
    @26
    @27
    cvv
    @27
    eqid
    fnmpt
    syl
    @0
    @20
    cT
    @27
    vx
    vz
    cD
    cT
    cvv
    vw
    pmtrrn.t
    pmtrfval
    fneq1d
    mpbird
    vy
    @20
    cF
    cT
    fvelrnb
    syl
    cR
    @9
    cF
    pmtrrn.r
    eleq2i
    @21
    @16
    @19
    @11
    @13
    vy
    vx
    @15
    @18
    @10
    c2o
    cen
    breq1
    rexrab
    bicomi
    3bitr4g
    @0
    @14
    @7
    vy
    @15
    @10
    @15
    wcel
    @10
    cD
    wss
    #
    @0
    @14
    @7
    wi
    @10
    cD
    elpwi
    @0
    @30
    @11
    @13
    @7
    @0
    @30
    @11
    @13
    @7
    wi
    @0
    @30
    @11
    w3a
    #
    @0
    @12
    cid
    cdif
    #
    cdm
    #
    cD
    wss
    #
    @33
    c2o
    cen
    wbr
    #
    w3a
    #
    @12
    @33
    cT
    cfv
    #
    wceq
    #
    wa
    #
    @13
    @7
    @31
    @36
    @38
    @31
    @0
    @34
    @35
    @0
    @30
    @11
    simp1
    @31
    @33
    @10
    cD
    cD
    @10
    cT
    cvv
    pmtrrn.t
    pmtrmvd
    #
    @0
    @30
    @11
    simp2
    eqsstrd
    @31
    @33
    @10
    c2o
    cen
    @40
    @0
    @30
    @11
    simp3
    eqbrtrd
    3jca
    @31
    @10
    @33
    cT
    @31
    @33
    @10
    @40
    eqcomd
    fveq2d
    jca
    @13
    @33
    cP
    wceq
    #
    @39
    @7
    wb
    @13
    @33
    cF
    cid
    cdif
    #
    cdm
    cP
    @13
    @32
    @42
    @12
    cF
    cid
    difeq1
    dmeqd
    pmtrfrn.p
    syl6eqr
    @13
    @41
    wa
    #
    @36
    @4
    @38
    @6
    @41
    @36
    @4
    wb
    @13
    @41
    @34
    @2
    @35
    @3
    @0
    @33
    cP
    cD
    sseq1
    @33
    cP
    c2o
    cen
    breq1
    3anbi23d
    adantl
    @43
    @12
    cF
    @37
    @5
    @13
    @41
    simpl
    @41
    @37
    @5
    wceq
    @13
    @33
    cP
    cT
    fveq2
    adantl
    eqeq12d
    anbi12d
    mpdan
    syl5ibcom
    3exp
    imp4a
    syl5
    rexlimdv
    sylbid
    mpcom
end
