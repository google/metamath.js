include "cfv.mm"
include "wceq.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "cmpst.mm"
include "wrex.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "eqid.mm"
include "msrf.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "mp2b.mm"
include "c1st.mm"
include "cmvrs.mm"
include "c2nd.mm"
include "csn.mm"
include "cun.mm"
include "cima.mm"
include "cuni.mm"
include "cxp.mm"
include "cin.mm"
include "cotp.mm"
include "mpst123.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeltrrd.mm"
include "msrval.mm"
include "syl.mm"
include "eqtrd.mm"
include "ffvelrni.mm"
include "inass.mm"
include "inidm.mm"
include "ineq2i.mm"
include "eqtri.mm"
include "a1i.mm"
include "oteq1d.mm"
include "3eqtr4d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "mstaval.mm"
include "eleq2s.mm"

theorem msrid
  let cR: class R
  let cS: class S
  let cT: class T
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  assume mstaval.r: |- R = ( mStRed ` T )
  assume mstaval.s: |- S = ( mStat ` T )


  assert |- ( X e. S -> ( R ` X ) = X )

  proof
    cX
    cR
    cfv
    #
    cX
    wceq
    #
    cX
    cR
    crn
    #
    cS
    cX
    @2
    wcel
    #
    vs
    cv
    #
    cR
    cfv
    #
    cX
    wceq
    #
    vs
    cT
    cmpst
    cfv
    #
    wrex
    #
    @1
    @7
    @7
    cR
    wf
    cR
    @7
    wfn
    @3
    @8
    wb
    @7
    cR
    cT
    @7
    eqid
    #
    mstaval.r
    msrf
    #
    @7
    @7
    cR
    ffn
    vs
    @7
    cX
    cR
    fvelrnb
    mp2b
    @6
    @1
    vs
    @7
    @4
    @7
    wcel
    #
    @5
    cR
    cfv
    #
    @5
    wceq
    @6
    @1
    @11
    @4
    c1st
    cfv
    #
    c1st
    cfv
    #
    cT
    cmvrs
    cfv
    #
    @13
    c2nd
    cfv
    #
    @4
    c2nd
    cfv
    #
    csn
    cun
    cima
    cuni
    #
    @18
    cxp
    #
    cin
    #
    @16
    @17
    cotp
    #
    cR
    cfv
    #
    @21
    @12
    @5
    @11
    @22
    @20
    @19
    cin
    #
    @16
    @17
    cotp
    #
    @21
    @11
    @21
    @7
    wcel
    @22
    @24
    wceq
    @11
    @5
    @21
    @7
    @11
    @5
    @14
    @16
    @17
    cotp
    #
    cR
    cfv
    #
    @21
    @11
    @4
    @25
    cR
    @7
    cT
    @4
    @9
    mpst123
    #
    fveq2d
    @11
    @25
    @7
    wcel
    @26
    @21
    wceq
    @11
    @4
    @25
    @7
    @27
    @11
    id
    eqeltrrd
    @17
    @14
    @7
    cR
    cT
    @16
    @15
    @18
    @15
    eqid
    #
    @9
    mstaval.r
    @18
    eqid
    #
    msrval
    syl
    eqtrd
    #
    @7
    @7
    @4
    cR
    @10
    ffvelrni
    eqeltrrd
    @17
    @20
    @7
    cR
    cT
    @16
    @15
    @18
    @28
    @9
    mstaval.r
    @29
    msrval
    syl
    @11
    @23
    @20
    @16
    @17
    @23
    @20
    wceq
    @11
    @23
    @14
    @19
    @19
    cin
    #
    cin
    @20
    @14
    @19
    @19
    inass
    @31
    @19
    @14
    @19
    inidm
    ineq2i
    eqtri
    a1i
    oteq1d
    eqtrd
    @11
    @5
    @21
    cR
    @30
    fveq2d
    @30
    3eqtr4d
    @6
    @12
    @0
    @5
    cX
    @5
    cX
    cR
    fveq2
    @6
    id
    eqeq12d
    syl5ibcom
    rexlimiv
    sylbi
    cR
    cS
    cT
    mstaval.r
    mstaval.s
    mstaval
    eleq2s
end
