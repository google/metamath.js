include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "csqrt.mm"
include "caddc.mm"
include "cn0.mm"
include "cxp.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmul.mm"
include "cmpt.mm"
include "ccnv.mm"
include "crmy.mm"
include "wceq.mm"
include "wa.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "cnveqd.mm"
include "adantr.mm"
include "id.mm"
include "oveq12d.mm"
include "oveqan12d.mm"
include "fveq12d.mm"
include "df-rmy.mm"
include "fvex.mm"
include "ovmpt2a.mm"

theorem rmyfval
  let cA: class A
  let cN: class N
  let vb: setvar b
  let va: setvar a
  let vn: setvar n

  disjoint A b
  disjoint N b
  disjoint a n
  disjoint a b
  disjoint A a
  disjoint b n
  disjoint A n
  disjoint N a
  disjoint N n
  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY N ) = ( 2nd ` ( `' ( b e. ( NN0 X. ZZ ) |-> ( ( 1st ` b ) + ( ( sqrt ` ( ( A ^ 2 ) - 1 ) ) x. ( 2nd ` b ) ) ) ) ` ( ( A + ( sqrt ` ( ( A ^ 2 ) - 1 ) ) ) ^ N ) ) ) )

  proof
    va
    vn
    cA
    cN
    c2
    cuz
    cfv
    cz
    va
    cv
    #
    @0
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    vn
    cv
    #
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
    @3
    @8
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
    #
    cfv
    #
    c2nd
    cfv
    cA
    cA
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    cN
    cexp
    co
    #
    vb
    @7
    @9
    @18
    @10
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    ccnv
    #
    cfv
    #
    c2nd
    cfv
    crmy
    @0
    cA
    wceq
    #
    @5
    cN
    wceq
    #
    wa
    #
    @15
    @25
    c2nd
    @28
    @6
    @20
    @14
    @24
    @26
    @14
    @24
    wceq
    @27
    @26
    @13
    @23
    @26
    vb
    @7
    @12
    @22
    @26
    @11
    @21
    @9
    caddc
    @26
    @3
    @18
    @10
    cmul
    @26
    @2
    @17
    csqrt
    @26
    @1
    @16
    c1
    cmin
    @0
    cA
    c2
    cexp
    oveq1
    oveq1d
    fveq2d
    #
    oveq1d
    oveq2d
    mpteq2dv
    cnveqd
    adantr
    @26
    @27
    @4
    @19
    @5
    cN
    cexp
    @26
    @0
    cA
    @3
    @18
    caddc
    @26
    id
    @29
    oveq12d
    @27
    id
    oveqan12d
    fveq12d
    fveq2d
    vn
    va
    vb
    df-rmy
    @25
    c2nd
    fvex
    ovmpt2a
end
