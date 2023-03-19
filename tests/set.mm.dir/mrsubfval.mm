include "cvv.mm"
include "wcel.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cun.mm"
include "cv.mm"
include "cs1.mm"
include "cif.mm"
include "cmpt.mm"
include "ccom.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cdm.mm"
include "cpm.mm"
include "mrsubffval.mm"
include "adantr.mm"
include "dmeq.mm"
include "fdm.mm"
include "ad2antrl.mm"
include "sylan9eqr.mm"
include "eleq2d.mm"
include "simpr.mm"
include "fveq1d.mm"
include "ifbieq1d.mm"
include "mpteq2dv.mm"
include "coeq1d.mm"
include "oveq2d.mm"
include "cmrex.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cmvar.mm"
include "simprl.mm"
include "simprr.mm"
include "elpm2r.mm"
include "syl22anc.mm"
include "mptex.mm"
include "fvmptd.mm"
include "ex.mm"
include "wn.mm"
include "c0.mm"
include "0fv.mm"
include "cmrsub.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "mpteq1d.mm"
include "mpt0.mm"
include "syl6eq.mm"
include "3eqtr4a.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem mrsubfval
  let vv: setvar v
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let ve: setvar e
  let cF: class F
  let cG: class G
  let cV: class V
  let vf: setvar f
  let vt: setvar t
  let cX: class X
  assume mrsubffval.c: |- C = ( mCN ` T )
  assume mrsubffval.v: |- V = ( mVR ` T )
  assume mrsubffval.r: |- R = ( mREx ` T )
  assume mrsubffval.s: |- S = ( mRSubst ` T )
  assume mrsubffval.g: |- G = ( freeMnd ` ( C u. V ) )

  disjoint e v
  disjoint A e
  disjoint A v
  disjoint C e
  disjoint C v
  disjoint F e
  disjoint F v
  disjoint R e
  disjoint R v
  disjoint G e
  disjoint T e
  disjoint T v
  disjoint V e
  disjoint V v
  disjoint e f
  disjoint f v
  disjoint A f
  disjoint e t
  disjoint f t
  disjoint C f
  disjoint t v
  disjoint C t
  disjoint F f
  disjoint R f
  disjoint R t
  disjoint X e
  disjoint X v
  disjoint G f
  disjoint G t
  disjoint T f
  disjoint T t
  disjoint V f
  disjoint V t
  assert |- ( ( F : A --> R /\ A C_ V ) -> ( S ` F ) = ( e e. R |-> ( G gsum ( ( v e. ( C u. V ) |-> if ( v e. A , ( F ` v ) , <" v "> ) ) o. e ) ) ) )

  proof
    cT
    cvv
    wcel
    #
    cA
    cR
    cF
    wf
    #
    cA
    cV
    wss
    #
    wa
    #
    cF
    cS
    cfv
    #
    ve
    cR
    cG
    vv
    cC
    cV
    cun
    #
    vv
    cv
    #
    cA
    wcel
    #
    @6
    cF
    cfv
    #
    @6
    cs1
    #
    cif
    #
    cmpt
    #
    ve
    cv
    #
    ccom
    #
    cgsu
    co
    #
    cmpt
    #
    wceq
    #
    wi
    @0
    @3
    @16
    @0
    @3
    wa
    #
    vf
    cF
    ve
    cR
    cG
    vv
    @5
    @6
    vf
    cv
    #
    cdm
    #
    wcel
    #
    @6
    @18
    cfv
    #
    @9
    cif
    #
    cmpt
    #
    @12
    ccom
    #
    cgsu
    co
    #
    cmpt
    #
    @15
    cR
    cV
    cpm
    co
    #
    cS
    cvv
    @0
    cS
    vf
    @27
    @26
    cmpt
    wceq
    @3
    vv
    cC
    cR
    cS
    cT
    ve
    vf
    cG
    cV
    cvv
    mrsubffval.c
    mrsubffval.v
    mrsubffval.r
    mrsubffval.s
    mrsubffval.g
    mrsubffval
    adantr
    @17
    @18
    cF
    wceq
    #
    wa
    #
    ve
    cR
    @25
    @14
    @29
    @24
    @13
    cG
    cgsu
    @29
    @23
    @11
    @12
    @29
    vv
    @5
    @22
    @10
    @29
    @20
    @7
    @21
    @8
    @9
    @29
    @19
    cA
    @6
    @28
    @17
    @19
    cF
    cdm
    #
    cA
    @18
    cF
    dmeq
    @1
    @30
    cA
    wceq
    @0
    @2
    cA
    cR
    cF
    fdm
    ad2antrl
    sylan9eqr
    eleq2d
    @29
    @6
    @18
    cF
    @17
    @28
    simpr
    fveq1d
    ifbieq1d
    mpteq2dv
    coeq1d
    oveq2d
    mpteq2dv
    @17
    cR
    cvv
    wcel
    #
    cV
    cvv
    wcel
    #
    @1
    @2
    cF
    @27
    wcel
    @31
    @17
    cR
    cT
    cmrex
    cfv
    #
    cvv
    mrsubffval.r
    cT
    cmrex
    fvex
    eqeltri
    #
    a1i
    @32
    @17
    cV
    cT
    cmvar
    cfv
    cvv
    mrsubffval.v
    cT
    cmvar
    fvex
    eqeltri
    a1i
    @0
    @1
    @2
    simprl
    @0
    @1
    @2
    simprr
    cR
    cV
    cA
    cF
    cvv
    cvv
    elpm2r
    syl22anc
    @15
    cvv
    wcel
    @17
    ve
    cR
    @14
    @34
    mptex
    a1i
    fvmptd
    ex
    @0
    wn
    #
    @16
    @3
    @35
    cF
    c0
    cfv
    c0
    @4
    @15
    cF
    0fv
    @35
    cF
    cS
    c0
    @35
    cS
    cT
    cmrsub
    cfv
    c0
    mrsubffval.s
    cT
    cmrsub
    fvprc
    syl5eq
    fveq1d
    @35
    @15
    ve
    c0
    @14
    cmpt
    c0
    @35
    ve
    cR
    c0
    @14
    @35
    cR
    @33
    c0
    mrsubffval.r
    cT
    cmrex
    fvprc
    syl5eq
    mpteq1d
    ve
    @14
    mpt0
    syl6eq
    3eqtr4a
    a1d
    pm2.61i
end
