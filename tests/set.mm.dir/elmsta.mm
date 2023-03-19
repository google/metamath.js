include "cotp.mm"
include "wcel.mm"
include "cxp.mm"
include "wss.mm"
include "wa.mm"
include "mstapst.mm"
include "sseli.mm"
include "cin.mm"
include "c1st.mm"
include "cfv.mm"
include "cmsr.mm"
include "wceq.mm"
include "eqid.mm"
include "msrval.mm"
include "syl.mm"
include "msrid.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "cvv.mm"
include "inss1.mm"
include "w3a.mm"
include "mpstrcl.mm"
include "simp1d.mm"
include "ssexg.mm"
include "sylancr.mm"
include "simp2d.mm"
include "simp3d.mm"
include "ot1stg.mm"
include "syl3anc.mm"
include "3eqtr3d.mm"
include "inss2.mm"
include "syl6eqssr.mm"
include "jca.mm"
include "crn.mm"
include "adantr.mm"
include "simpr.mm"
include "df-ss.mm"
include "sylib.mm"
include "oteq1d.mm"
include "eqtrd.mm"
include "wfn.mm"
include "wf.mm"
include "msrf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "simpl.mm"
include "fnfvelrn.mm"
include "eqeltrrd.mm"
include "mstaval.mm"
include "syl6eleqr.mm"
include "impbii.mm"

theorem elmsta
  let cA: class A
  let cD: class D
  let cP: class P
  let cS: class S
  let cT: class T
  let cH: class H
  let cV: class V
  let cZ: class Z
  assume mstapst.p: |- P = ( mPreSt ` T )
  assume mstapst.s: |- S = ( mStat ` T )
  assume elmsta.v: |- V = ( mVars ` T )
  assume elmsta.z: |- Z = U. ( V " ( H u. { A } ) )


  assert |- ( <. D , H , A >. e. S <-> ( <. D , H , A >. e. P /\ D C_ ( Z X. Z ) ) )

  proof
    cD
    cH
    cA
    cotp
    #
    cS
    wcel
    #
    @0
    cP
    wcel
    #
    cD
    cZ
    cZ
    cxp
    #
    wss
    #
    wa
    #
    @1
    @2
    @4
    cS
    cP
    @0
    cP
    cS
    cT
    mstapst.p
    mstapst.s
    mstapst
    sseli
    #
    @1
    cD
    cD
    @3
    cin
    #
    @3
    @1
    @7
    cH
    cA
    cotp
    #
    c1st
    cfv
    #
    c1st
    cfv
    #
    @0
    c1st
    cfv
    #
    c1st
    cfv
    #
    @7
    cD
    @1
    @9
    @11
    c1st
    @1
    @8
    @0
    c1st
    @1
    @0
    cT
    cmsr
    cfv
    #
    cfv
    #
    @8
    @0
    @1
    @2
    @14
    @8
    wceq
    #
    @6
    cA
    cD
    cP
    @13
    cT
    cH
    cV
    cZ
    elmsta.v
    mstapst.p
    @13
    eqid
    #
    elmsta.z
    msrval
    #
    syl
    @13
    cS
    cT
    @0
    @16
    mstapst.s
    msrid
    eqtr3d
    fveq2d
    fveq2d
    @1
    @7
    cvv
    wcel
    #
    cH
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    @10
    @7
    wceq
    @1
    @7
    cD
    wss
    cD
    cvv
    wcel
    #
    @18
    cD
    @3
    inss1
    @1
    @21
    @19
    @20
    @1
    @2
    @21
    @19
    @20
    w3a
    #
    @6
    cA
    cD
    cP
    cT
    cH
    mstapst.p
    mpstrcl
    syl
    #
    simp1d
    @7
    cD
    cvv
    ssexg
    sylancr
    @1
    @21
    @19
    @20
    @23
    simp2d
    @1
    @21
    @19
    @20
    @23
    simp3d
    @7
    cH
    cA
    cvv
    cvv
    cvv
    ot1stg
    syl3anc
    @1
    @22
    @12
    cD
    wceq
    @23
    cD
    cH
    cA
    cvv
    cvv
    cvv
    ot1stg
    syl
    3eqtr3d
    cD
    @3
    inss2
    syl6eqssr
    jca
    @5
    @0
    @13
    crn
    #
    cS
    @5
    @14
    @0
    @24
    @5
    @14
    @8
    @0
    @2
    @15
    @4
    @17
    adantr
    @5
    @7
    cD
    cH
    cA
    @5
    @4
    @7
    cD
    wceq
    @2
    @4
    simpr
    cD
    @3
    df-ss
    sylib
    oteq1d
    eqtrd
    @5
    @13
    cP
    wfn
    #
    @2
    @14
    @24
    wcel
    cP
    cP
    @13
    wf
    @25
    cP
    @13
    cT
    mstapst.p
    @16
    msrf
    cP
    cP
    @13
    ffn
    ax-mp
    @2
    @4
    simpl
    cP
    @0
    @13
    fnfvelrn
    sylancr
    eqeltrrd
    @13
    cS
    cT
    @16
    mstapst.s
    mstaval
    syl6eleqr
    impbii
end
