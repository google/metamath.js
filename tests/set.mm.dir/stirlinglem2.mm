include "cn.mm"
include "wcel.mm"
include "cfv.mm"
include "cfa.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "ceu.mm"
include "cdiv.mm"
include "cexp.mm"
include "crp.mm"
include "wceq.mm"
include "cn0.mm"
include "nnnn0.mm"
include "faccl.mm"
include "nnrp.mm"
include "3syl.mm"
include "2rp.mm"
include "a1i.mm"
include "rpmulcld.mm"
include "rpsqrtcld.mm"
include "epr.mm"
include "rpdivcld.mm"
include "nnz.mm"
include "rpexpcld.mm"
include "wa.mm"
include "cv.mm"
include "cmpt.mm"
include "fveq2.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq1.mm"
include "id.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "simpr.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "simpl.mm"
include "fvmptd.mm"
include "mpdan.mm"
include "eqeltrd.mm"

theorem stirlinglem2
  let cA: class A
  let vn: setvar n
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  assume stirlinglem2.1: |- A = ( n e. NN |-> ( ( ! ` n ) / ( ( sqrt ` ( 2 x. n ) ) x. ( ( n / _e ) ^ n ) ) ) )


  assert |- ( N e. NN -> ( A ` N ) e. RR+ )

  proof
    cN
    cn
    wcel
    #
    cN
    cA
    cfv
    #
    cN
    cfa
    cfv
    #
    c2
    cN
    cmul
    co
    #
    csqrt
    cfv
    #
    cN
    ceu
    cdiv
    co
    #
    cN
    cexp
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    crp
    @0
    @8
    crp
    wcel
    #
    @1
    @8
    wceq
    @0
    @2
    @7
    @0
    cN
    cn0
    wcel
    @2
    cn
    wcel
    @2
    crp
    wcel
    cN
    nnnn0
    cN
    faccl
    @2
    nnrp
    3syl
    @0
    @4
    @6
    @0
    @3
    @0
    c2
    cN
    c2
    crp
    wcel
    @0
    2rp
    a1i
    cN
    nnrp
    #
    rpmulcld
    rpsqrtcld
    @0
    @5
    cN
    @0
    cN
    ceu
    @10
    ceu
    crp
    wcel
    @0
    epr
    a1i
    rpdivcld
    cN
    nnz
    rpexpcld
    rpmulcld
    rpdivcld
    #
    @0
    @9
    wa
    #
    vk
    cN
    vk
    cv
    #
    cfa
    cfv
    #
    c2
    @13
    cmul
    co
    #
    csqrt
    cfv
    #
    @13
    ceu
    cdiv
    co
    #
    @13
    cexp
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    @8
    cn
    cA
    crp
    cA
    vk
    cn
    @20
    cmpt
    #
    wceq
    @12
    cA
    vn
    cn
    vn
    cv
    #
    cfa
    cfv
    #
    c2
    @22
    cmul
    co
    #
    csqrt
    cfv
    #
    @22
    ceu
    cdiv
    co
    #
    @22
    cexp
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    cmpt
    @21
    stirlinglem2.1
    vn
    vk
    cn
    @29
    @20
    @22
    @13
    wceq
    #
    @23
    @14
    @28
    @19
    cdiv
    @22
    @13
    cfa
    fveq2
    @30
    @25
    @16
    @27
    @18
    cmul
    @30
    @24
    @15
    csqrt
    @22
    @13
    c2
    cmul
    oveq2
    fveq2d
    @30
    @26
    @17
    @22
    @13
    cexp
    @22
    @13
    ceu
    cdiv
    oveq1
    @30
    id
    oveq12d
    oveq12d
    oveq12d
    cbvmptv
    eqtri
    a1i
    @12
    @13
    cN
    wceq
    #
    wa
    #
    @14
    @2
    @19
    @7
    cdiv
    @32
    @13
    cN
    cfa
    @12
    @31
    simpr
    #
    fveq2d
    @32
    @16
    @4
    @18
    @6
    cmul
    @32
    @15
    @3
    csqrt
    @32
    @13
    cN
    c2
    cmul
    @33
    oveq2d
    fveq2d
    @32
    @17
    @5
    @13
    cN
    cexp
    @32
    @13
    cN
    ceu
    cdiv
    @33
    oveq1d
    @33
    oveq12d
    oveq12d
    oveq12d
    @0
    @9
    simpl
    @0
    @9
    simpr
    fvmptd
    mpdan
    @11
    eqeltrd
end
