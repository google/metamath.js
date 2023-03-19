include "cn0.mm"
include "wcel.mm"
include "cc.mm"
include "cexp.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "abs1.mm"
include "exp0.mm"
include "abscl.mm"
include "recnd.mm"
include "exp0d.mm"
include "3eqtr4a.mm"
include "wa.mm"
include "cmul.mm"
include "oveq1.mm"
include "adantl.mm"
include "expp1.mm"
include "expcl.mm"
include "simpl.mm"
include "absmul.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "adantr.mm"
include "sylan.mm"
include "3eqtr4d.mm"
include "exp31.mm"
include "com12.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem absexp
  let cA: class A
  let cN: class N
  let vj: setvar j
  let vk: setvar k


  assert |- ( ( A e. CC /\ N e. NN0 ) -> ( abs ` ( A ^ N ) ) = ( ( abs ` A ) ^ N ) )

  proof
    cN
    cn0
    wcel
    cA
    cc
    wcel
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
    @0
    cA
    vj
    cv
    #
    cexp
    co
    #
    cabs
    cfv
    #
    @3
    @6
    cexp
    co
    #
    wceq
    #
    wi
    @0
    cA
    cc0
    cexp
    co
    #
    cabs
    cfv
    #
    @3
    cc0
    cexp
    co
    #
    wceq
    #
    wi
    @0
    cA
    vk
    cv
    #
    cexp
    co
    #
    cabs
    cfv
    #
    @3
    @15
    cexp
    co
    #
    wceq
    #
    wi
    @0
    cA
    @15
    c1
    caddc
    co
    #
    cexp
    co
    #
    cabs
    cfv
    #
    @3
    @20
    cexp
    co
    #
    wceq
    #
    wi
    @0
    @5
    wi
    vj
    vk
    cN
    @6
    cc0
    wceq
    #
    @10
    @14
    @0
    @25
    @8
    @12
    @9
    @13
    @25
    @7
    @11
    cabs
    @6
    cc0
    cA
    cexp
    oveq2
    fveq2d
    @6
    cc0
    @3
    cexp
    oveq2
    eqeq12d
    imbi2d
    @6
    @15
    wceq
    #
    @10
    @19
    @0
    @26
    @8
    @17
    @9
    @18
    @26
    @7
    @16
    cabs
    @6
    @15
    cA
    cexp
    oveq2
    fveq2d
    @6
    @15
    @3
    cexp
    oveq2
    eqeq12d
    imbi2d
    @6
    @20
    wceq
    #
    @10
    @24
    @0
    @27
    @8
    @22
    @9
    @23
    @27
    @7
    @21
    cabs
    @6
    @20
    cA
    cexp
    oveq2
    fveq2d
    @6
    @20
    @3
    cexp
    oveq2
    eqeq12d
    imbi2d
    @6
    cN
    wceq
    #
    @10
    @5
    @0
    @28
    @8
    @2
    @9
    @4
    @28
    @7
    @1
    cabs
    @6
    cN
    cA
    cexp
    oveq2
    fveq2d
    @6
    cN
    @3
    cexp
    oveq2
    eqeq12d
    imbi2d
    @0
    c1
    cabs
    cfv
    c1
    @12
    @13
    abs1
    @0
    @11
    c1
    cabs
    cA
    exp0
    fveq2d
    @0
    @3
    @0
    @3
    cA
    abscl
    recnd
    #
    exp0d
    3eqtr4a
    @15
    cn0
    wcel
    #
    @0
    @19
    @24
    @0
    @30
    @19
    @24
    wi
    @0
    @30
    @19
    @24
    @0
    @30
    wa
    #
    @19
    wa
    @17
    @3
    cmul
    co
    #
    @18
    @3
    cmul
    co
    #
    @22
    @23
    @19
    @32
    @33
    wceq
    @31
    @17
    @18
    @3
    cmul
    oveq1
    adantl
    @31
    @22
    @32
    wceq
    @19
    @31
    @22
    @16
    cA
    cmul
    co
    #
    cabs
    cfv
    #
    @32
    @31
    @21
    @34
    cabs
    cA
    @15
    expp1
    fveq2d
    @31
    @16
    cc
    wcel
    @0
    @35
    @32
    wceq
    cA
    @15
    expcl
    @0
    @30
    simpl
    @16
    cA
    absmul
    syl2anc
    eqtrd
    adantr
    @31
    @23
    @33
    wceq
    #
    @19
    @0
    @3
    cc
    wcel
    @30
    @36
    @29
    @3
    @15
    expp1
    sylan
    adantr
    3eqtr4d
    exp31
    com12
    a2d
    nn0ind
    impcom
end
