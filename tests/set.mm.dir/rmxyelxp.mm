include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cn0.mm"
include "cxp.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "csqrt.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmpt.mm"
include "wf1o.mm"
include "ccnv.mm"
include "rmxypairf1o.mm"
include "adantr.mm"
include "rmxyelqirr.mm"
include "f1ocnvdm.mm"
include "syl2anc.mm"

theorem rmxyelxp
  let cA: class A
  let cN: class N
  let vb: setvar b
  let va: setvar a
  let vc: setvar c
  let vd: setvar d

  disjoint A b
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint A c
  disjoint A d
  disjoint N a
  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( `' ( b e. ( NN0 X. ZZ ) |-> ( ( 1st ` b ) + ( ( sqrt ` ( ( A ^ 2 ) - 1 ) ) x. ( 2nd ` b ) ) ) ) ` ( ( A + ( sqrt ` ( ( A ^ 2 ) - 1 ) ) ) ^ N ) ) e. ( NN0 X. ZZ ) )

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
    cn0
    cz
    cxp
    #
    va
    cv
    vc
    cv
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
    vb
    @2
    vb
    cv
    #
    c1st
    cfv
    @3
    @5
    c2nd
    cfv
    cmul
    co
    caddc
    co
    cmpt
    #
    wf1o
    #
    cA
    @3
    caddc
    co
    cN
    cexp
    co
    #
    @4
    wcel
    @8
    @6
    ccnv
    cfv
    @2
    wcel
    @0
    @7
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
    @2
    @4
    @8
    @6
    f1ocnvdm
    syl2anc
end
