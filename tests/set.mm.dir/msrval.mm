include "cotp.mm"
include "wcel.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "csn.mm"
include "cun.mm"
include "cima.mm"
include "cuni.mm"
include "cxp.mm"
include "csb.mm"
include "cin.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "msrfval.mm"
include "a1i.mm"
include "wa.mm"
include "fvexd.mm"
include "simpllr.mm"
include "fveq2d.mm"
include "cfn.mm"
include "cmex.mm"
include "cmdv.mm"
include "wss.mm"
include "ccnv.mm"
include "eqid.mm"
include "elmpst.mm"
include "simp1bi.mm"
include "simpld.mm"
include "ad3antrrr.mm"
include "fvex.mm"
include "ssex.mm"
include "syl.mm"
include "simp2bi.mm"
include "simprd.mm"
include "simp3bi.mm"
include "ot1stg.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "cmvrs.mm"
include "eqeltri.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "uniex.mm"
include "id.mm"
include "simplr.mm"
include "ot2ndg.mm"
include "3eqtrd.mm"
include "simpr.mm"
include "ot3rdg.mm"
include "sneqd.mm"
include "uneq12d.mm"
include "imaeq2d.mm"
include "unieqd.mm"
include "syl6eqr.mm"
include "sylan9eqr.mm"
include "sqxpeqd.mm"
include "csbied.mm"
include "ineq12d.mm"
include "oteq123d.mm"
include "otex.mm"
include "fvmptd.mm"

theorem msrval
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let cH: class H
  let cV: class V
  let cZ: class Z
  let va: setvar a
  let vh: setvar h
  let vs: setvar s
  let vz: setvar z
  let vt: setvar t
  assume msrfval.v: |- V = ( mVars ` T )
  assume msrfval.p: |- P = ( mPreSt ` T )
  assume msrfval.r: |- R = ( mStRed ` T )
  assume msrval.z: |- Z = U. ( V " ( H u. { A } ) )


  assert |- ( <. D , H , A >. e. P -> ( R ` <. D , H , A >. ) = <. ( D i^i ( Z X. Z ) ) , H , A >. )

  proof
    cD
    cH
    cA
    cotp
    #
    cP
    wcel
    #
    vs
    @0
    vh
    vs
    cv
    #
    c1st
    cfv
    #
    c2nd
    cfv
    #
    va
    @2
    c2nd
    cfv
    #
    @3
    c1st
    cfv
    #
    vz
    cV
    vh
    cv
    #
    va
    cv
    #
    csn
    #
    cun
    #
    cima
    #
    cuni
    #
    vz
    cv
    #
    @13
    cxp
    #
    csb
    #
    cin
    #
    @7
    @8
    cotp
    #
    csb
    #
    csb
    #
    cD
    cZ
    cZ
    cxp
    #
    cin
    #
    cH
    cA
    cotp
    #
    cP
    cR
    cvv
    cR
    vs
    cP
    @19
    cmpt
    wceq
    @1
    vz
    cP
    cR
    cT
    vh
    cV
    vs
    va
    msrfval.v
    msrfval.p
    msrfval.r
    msrfval
    a1i
    @1
    @2
    @0
    wceq
    #
    wa
    #
    vh
    @4
    @18
    @22
    cvv
    @24
    @3
    c2nd
    fvexd
    @24
    @7
    @4
    wceq
    #
    wa
    #
    va
    @5
    @17
    @22
    cvv
    @26
    @2
    c2nd
    fvexd
    @26
    @8
    @5
    wceq
    #
    wa
    #
    @16
    @21
    @7
    cH
    @8
    cA
    @28
    @6
    cD
    @15
    @20
    @28
    @6
    @0
    c1st
    cfv
    #
    c1st
    cfv
    #
    cD
    @28
    @3
    @29
    c1st
    @28
    @2
    @0
    c1st
    @1
    @23
    @25
    @27
    simpllr
    #
    fveq2d
    #
    fveq2d
    @28
    cD
    cvv
    wcel
    #
    cH
    cfn
    wcel
    #
    cA
    cT
    cmex
    cfv
    #
    wcel
    #
    @30
    cD
    wceq
    @28
    cD
    cT
    cmdv
    cfv
    #
    wss
    #
    @33
    @1
    @38
    @23
    @25
    @27
    @1
    @38
    cD
    ccnv
    cD
    wceq
    #
    @1
    @38
    @39
    wa
    #
    cH
    @35
    wss
    #
    @34
    wa
    #
    @36
    cA
    cD
    cP
    cT
    @35
    cH
    @37
    @37
    eqid
    @35
    eqid
    msrfval.p
    elmpst
    #
    simp1bi
    simpld
    ad3antrrr
    cD
    @37
    cT
    cmdv
    fvex
    ssex
    syl
    #
    @1
    @34
    @23
    @25
    @27
    @1
    @41
    @34
    @1
    @40
    @42
    @36
    @43
    simp2bi
    simprd
    ad3antrrr
    #
    @1
    @36
    @23
    @25
    @27
    @1
    @40
    @42
    @36
    @43
    simp3bi
    ad3antrrr
    #
    cD
    cH
    cA
    cvv
    cfn
    @35
    ot1stg
    syl3anc
    eqtrd
    @28
    vz
    @12
    @14
    @20
    cvv
    @12
    cvv
    wcel
    @28
    @11
    cV
    cvv
    wcel
    @11
    cvv
    wcel
    cV
    cT
    cmvrs
    cfv
    cvv
    msrfval.v
    cT
    cmvrs
    fvex
    eqeltri
    cV
    @10
    cvv
    imaexg
    ax-mp
    uniex
    a1i
    @28
    @13
    @12
    wceq
    #
    wa
    @13
    cZ
    @47
    @28
    @13
    @12
    cZ
    @47
    id
    @28
    @12
    cV
    cH
    cA
    csn
    #
    cun
    #
    cima
    #
    cuni
    cZ
    @28
    @11
    @50
    @28
    @10
    @49
    cV
    @28
    @7
    cH
    @9
    @48
    @28
    @7
    @4
    @29
    c2nd
    cfv
    #
    cH
    @24
    @25
    @27
    simplr
    @28
    @3
    @29
    c2nd
    @32
    fveq2d
    @28
    @33
    @34
    @36
    @51
    cH
    wceq
    @44
    @45
    @46
    cD
    cH
    cA
    cvv
    cfn
    @35
    ot2ndg
    syl3anc
    3eqtrd
    #
    @28
    @8
    cA
    @28
    @8
    @5
    @0
    c2nd
    cfv
    #
    cA
    @26
    @27
    simpr
    @28
    @2
    @0
    c2nd
    @31
    fveq2d
    @28
    @36
    @53
    cA
    wceq
    @46
    cD
    cH
    cA
    @35
    ot3rdg
    syl
    3eqtrd
    #
    sneqd
    uneq12d
    imaeq2d
    unieqd
    msrval.z
    syl6eqr
    sylan9eqr
    sqxpeqd
    csbied
    ineq12d
    @52
    @54
    oteq123d
    csbied
    csbied
    @1
    id
    @22
    cvv
    wcel
    @1
    @21
    cH
    cA
    otex
    a1i
    fvmptd
end
