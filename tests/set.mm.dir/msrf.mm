include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmvrs.mm"
include "csn.mm"
include "cun.mm"
include "cima.mm"
include "cuni.mm"
include "cxp.mm"
include "csb.mm"
include "cin.mm"
include "cotp.mm"
include "otex.mm"
include "csbex.mm"
include "eqid.mm"
include "msrfval.mm"
include "fnmpti.mm"
include "mpst123.mm"
include "fveq2d.mm"
include "wceq.mm"
include "id.mm"
include "eqeltrrd.mm"
include "msrval.mm"
include "syl.mm"
include "eqtrd.mm"
include "cmdv.mm"
include "wss.mm"
include "ccnv.mm"
include "wa.mm"
include "cmex.mm"
include "cfn.mm"
include "inss1.mm"
include "w3a.mm"
include "elmpst.mm"
include "sylib.mm"
include "simp1d.mm"
include "simpld.mm"
include "syl5ss.mm"
include "cnvin.mm"
include "simprd.mm"
include "cnvxp.mm"
include "a1i.mm"
include "ineq12d.mm"
include "syl5eq.mm"
include "jca.mm"
include "simp2d.mm"
include "simp3d.mm"
include "syl3anbrc.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"

theorem msrf
  let cP: class P
  let cR: class R
  let cT: class T
  let va: setvar a
  let vh: setvar h
  let vs: setvar s
  let vz: setvar z
  let vd: setvar d
  assume mpstssv.p: |- P = ( mPreSt ` T )
  assume msrf.r: |- R = ( mStRed ` T )


  assert |- R : P --> P

  proof
    cP
    cP
    cR
    wf
    cR
    cP
    wfn
    vs
    cv
    #
    cR
    cfv
    #
    cP
    wcel
    #
    vs
    cP
    wral
    vs
    cP
    vh
    @0
    c1st
    cfv
    #
    c2nd
    cfv
    #
    va
    @0
    c2nd
    cfv
    #
    @3
    c1st
    cfv
    #
    vz
    cT
    cmvrs
    cfv
    #
    vh
    cv
    #
    va
    cv
    #
    csn
    cun
    cima
    cuni
    vz
    cv
    #
    @10
    cxp
    csb
    cin
    #
    @8
    @9
    cotp
    #
    csb
    #
    csb
    cR
    vh
    @4
    @13
    va
    @5
    @12
    @11
    @8
    @9
    otex
    csbex
    csbex
    vz
    cP
    cR
    cT
    vh
    @7
    vs
    va
    @7
    eqid
    #
    mpstssv.p
    msrf.r
    msrfval
    fnmpti
    @2
    vs
    cP
    @0
    cP
    wcel
    #
    @1
    @6
    @7
    @4
    @5
    csn
    cun
    cima
    cuni
    #
    @16
    cxp
    #
    cin
    #
    @4
    @5
    cotp
    #
    cP
    @15
    @1
    @6
    @4
    @5
    cotp
    #
    cR
    cfv
    #
    @19
    @15
    @0
    @20
    cR
    cP
    cT
    @0
    mpstssv.p
    mpst123
    #
    fveq2d
    @15
    @20
    cP
    wcel
    #
    @21
    @19
    wceq
    @15
    @0
    @20
    cP
    @22
    @15
    id
    eqeltrrd
    #
    @5
    @6
    cP
    cR
    cT
    @4
    @7
    @16
    @14
    mpstssv.p
    msrf.r
    @16
    eqid
    msrval
    syl
    eqtrd
    @15
    @18
    cT
    cmdv
    cfv
    #
    wss
    #
    @18
    ccnv
    #
    @18
    wceq
    #
    wa
    @4
    cT
    cmex
    cfv
    #
    wss
    @4
    cfn
    wcel
    wa
    #
    @5
    @29
    wcel
    #
    @19
    cP
    wcel
    @15
    @26
    @28
    @15
    @18
    @6
    @25
    @6
    @17
    inss1
    @15
    @6
    @25
    wss
    #
    @6
    ccnv
    #
    @6
    wceq
    #
    @15
    @32
    @34
    wa
    #
    @30
    @31
    @15
    @23
    @35
    @30
    @31
    w3a
    @24
    @5
    @6
    cP
    cT
    @29
    @4
    @25
    @25
    eqid
    #
    @29
    eqid
    #
    mpstssv.p
    elmpst
    sylib
    #
    simp1d
    #
    simpld
    syl5ss
    @15
    @27
    @33
    @17
    ccnv
    #
    cin
    @18
    @6
    @17
    cnvin
    @15
    @33
    @6
    @40
    @17
    @15
    @32
    @34
    @39
    simprd
    @40
    @17
    wceq
    @15
    @16
    @16
    cnvxp
    a1i
    ineq12d
    syl5eq
    jca
    @15
    @35
    @30
    @31
    @38
    simp2d
    @15
    @35
    @30
    @31
    @38
    simp3d
    @5
    @18
    cP
    cT
    @29
    @4
    @25
    @36
    @37
    mpstssv.p
    elmpst
    syl3anbrc
    eqeltrd
    rgen
    vs
    cP
    cP
    cR
    ffnfv
    mpbir2an
end
