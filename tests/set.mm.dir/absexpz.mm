include "cz.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "cn0.mm"
include "cr.mm"
include "cneg.mm"
include "cn.mm"
include "wa.mm"
include "wo.mm"
include "cexp.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "elznn0nn.mm"
include "wi.mm"
include "absexp.mm"
include "ex.mm"
include "adantr.mm"
include "c1.mm"
include "cdiv.mm"
include "1cnd.mm"
include "simpll.mm"
include "nnnn0.mm"
include "ad2antll.mm"
include "expcld.mm"
include "simplr.mm"
include "nnz.mm"
include "expne0d.mm"
include "absdiv.mm"
include "syl3anc.mm"
include "abs1.mm"
include "oveq1i.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "simprl.mm"
include "recnd.mm"
include "expneg2.mm"
include "fveq2d.mm"
include "abscl.mm"
include "ad2antrr.mm"
include "3eqtr4d.mm"
include "jaod.mm"
include "3impia.mm"
include "syl3an3b.mm"

theorem absexpz
  let cA: class A
  let cN: class N


  assert |- ( ( A e. CC /\ A =/= 0 /\ N e. ZZ ) -> ( abs ` ( A ^ N ) ) = ( ( abs ` A ) ^ N ) )

  proof
    cN
    cz
    wcel
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cN
    cn0
    wcel
    #
    cN
    cr
    wcel
    #
    cN
    cneg
    #
    cn
    wcel
    #
    wa
    #
    wo
    #
    cA
    cN
    cexp
    co
    #
    cabs
    cfv
    #
    cA
    cabs
    cfv
    #
    cN
    cexp
    co
    #
    wceq
    #
    cN
    elznn0nn
    @0
    @1
    @7
    @12
    @0
    @1
    wa
    #
    @2
    @12
    @6
    @0
    @2
    @12
    wi
    @1
    @0
    @2
    @12
    cA
    cN
    absexp
    ex
    adantr
    @13
    @6
    @12
    @13
    @6
    wa
    #
    c1
    cA
    @4
    cexp
    co
    #
    cdiv
    co
    #
    cabs
    cfv
    #
    c1
    @10
    @4
    cexp
    co
    #
    cdiv
    co
    #
    @9
    @11
    @14
    @17
    c1
    cabs
    cfv
    #
    @15
    cabs
    cfv
    #
    cdiv
    co
    #
    @19
    @14
    c1
    cc
    wcel
    @15
    cc
    wcel
    @15
    cc0
    wne
    @17
    @22
    wceq
    @14
    1cnd
    @14
    cA
    @4
    @0
    @1
    @6
    simpll
    #
    @5
    @4
    cn0
    wcel
    #
    @13
    @3
    @4
    nnnn0
    ad2antll
    #
    expcld
    @14
    cA
    @4
    @23
    @0
    @1
    @6
    simplr
    @5
    @4
    cz
    wcel
    @13
    @3
    @4
    nnz
    ad2antll
    expne0d
    c1
    @15
    absdiv
    syl3anc
    @14
    @22
    c1
    @21
    cdiv
    co
    @19
    @20
    c1
    @21
    cdiv
    abs1
    oveq1i
    @14
    @21
    @18
    c1
    cdiv
    @14
    @0
    @24
    @21
    @18
    wceq
    @23
    @25
    cA
    @4
    absexp
    syl2anc
    oveq2d
    syl5eq
    eqtrd
    @14
    @8
    @16
    cabs
    @14
    @0
    cN
    cc
    wcel
    #
    @24
    @8
    @16
    wceq
    @23
    @14
    cN
    @13
    @3
    @5
    simprl
    recnd
    #
    @25
    cA
    cN
    expneg2
    syl3anc
    fveq2d
    @14
    @10
    cc
    wcel
    @26
    @24
    @11
    @19
    wceq
    @14
    @10
    @0
    @10
    cr
    wcel
    @1
    @6
    cA
    abscl
    ad2antrr
    recnd
    @27
    @25
    @10
    cN
    expneg2
    syl3anc
    3eqtr4d
    ex
    jaod
    3impia
    syl3an3b
end
