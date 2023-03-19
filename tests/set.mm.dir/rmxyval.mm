include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "crmx.mm"
include "co.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "csqrt.mm"
include "crmy.mm"
include "cmul.mm"
include "caddc.mm"
include "cn0.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmpt.mm"
include "ccnv.mm"
include "rmxfval.mm"
include "rmyfval.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "wceq.mm"
include "rmxyelxp.mm"
include "fveq2.mm"
include "weq.mm"
include "cbvmptv.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "wrex.mm"
include "cab.mm"
include "wf1o.mm"
include "rmxypairf1o.mm"
include "adantr.mm"
include "rmxyelqirr.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "3eqtr2d.mm"

theorem rmxyval
  let cA: class A
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( ( A rmX N ) + ( ( sqrt ` ( ( A ^ 2 ) - 1 ) ) x. ( A rmY N ) ) ) = ( ( A + ( sqrt ` ( ( A ^ 2 ) - 1 ) ) ) ^ N ) )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cA
    cN
    crmx
    co
    #
    cA
    c2
    cexp
    co
    c1
    cmin
    co
    csqrt
    cfv
    #
    cA
    cN
    crmy
    co
    #
    cmul
    co
    #
    caddc
    co
    cA
    @4
    caddc
    co
    cN
    cexp
    co
    #
    vb
    cn0
    cz
    cxp
    #
    vb
    cv
    #
    c1st
    cfv
    #
    @4
    @9
    c2nd
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    ccnv
    cfv
    #
    c1st
    cfv
    #
    @4
    @15
    c2nd
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @15
    @14
    cfv
    #
    @7
    @2
    @3
    @16
    @6
    @18
    caddc
    cA
    cN
    vb
    rmxfval
    @2
    @5
    @17
    @4
    cmul
    cA
    cN
    vb
    rmyfval
    oveq2d
    oveq12d
    @2
    @15
    @8
    wcel
    @20
    @19
    wceq
    cA
    cN
    vb
    rmxyelxp
    va
    @15
    va
    cv
    #
    c1st
    cfv
    #
    @4
    @21
    c2nd
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @19
    @8
    @14
    @21
    @15
    wceq
    #
    @22
    @16
    @24
    @18
    caddc
    @21
    @15
    c1st
    fveq2
    @26
    @23
    @17
    @4
    cmul
    @21
    @15
    c2nd
    fveq2
    oveq2d
    oveq12d
    vb
    va
    @8
    @13
    @25
    vb
    va
    weq
    #
    @10
    @22
    @12
    @24
    caddc
    @9
    @21
    c1st
    fveq2
    @27
    @11
    @23
    @4
    cmul
    @9
    @21
    c2nd
    fveq2
    oveq2d
    oveq12d
    cbvmptv
    @16
    @18
    caddc
    ovex
    fvmpt
    syl
    @2
    @8
    @21
    vc
    cv
    @4
    vd
    cv
    cmul
    co
    caddc
    co
    wceq
    vd
    cz
    wrex
    vc
    cn0
    wrex
    va
    cab
    #
    @14
    wf1o
    #
    @7
    @28
    wcel
    @20
    @7
    wceq
    @0
    @29
    @1
    cA
    va
    vb
    vc
    vd
    rmxypairf1o
    adantr
    cA
    cN
    va
    vc
    vd
    rmxyelqirr
    @8
    @28
    @7
    @14
    f1ocnvfv2
    syl2anc
    3eqtr2d
end
