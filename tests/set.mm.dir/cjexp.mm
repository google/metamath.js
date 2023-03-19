include "cn0.mm"
include "wcel.mm"
include "cc.mm"
include "cexp.mm"
include "co.mm"
include "ccj.mm"
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
include "exp0.mm"
include "cjcl.mm"
include "cr.mm"
include "1re.mm"
include "cjre.mm"
include "ax-mp.mm"
include "syl6eqr.mm"
include "syl.mm"
include "eqtr4d.mm"
include "wa.mm"
include "cmul.mm"
include "expp1.mm"
include "expcl.mm"
include "simpl.mm"
include "cjmul.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "adantr.mm"
include "oveq1.mm"
include "sylan.mm"
include "eqcomd.mm"
include "sylan9eqr.mm"
include "exp31.mm"
include "com12.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem cjexp
  let cA: class A
  let cN: class N
  let vj: setvar j
  let vk: setvar k


  assert |- ( ( A e. CC /\ N e. NN0 ) -> ( * ` ( A ^ N ) ) = ( ( * ` A ) ^ N ) )

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
    ccj
    cfv
    #
    cA
    ccj
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
    ccj
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
    ccj
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
    ccj
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
    ccj
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
    ccj
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
    ccj
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
    ccj
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
    ccj
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
    @12
    c1
    ccj
    cfv
    #
    @13
    @0
    @11
    c1
    ccj
    cA
    exp0
    fveq2d
    @0
    @3
    cc
    wcel
    #
    @13
    @29
    wceq
    cA
    cjcl
    #
    @30
    @13
    c1
    @29
    @3
    exp0
    c1
    cr
    wcel
    @29
    c1
    wceq
    1re
    c1
    cjre
    ax-mp
    syl6eqr
    syl
    eqtr4d
    @15
    cn0
    wcel
    #
    @0
    @19
    @24
    @0
    @32
    @19
    @24
    wi
    @0
    @32
    @19
    @24
    @0
    @32
    wa
    #
    @19
    wa
    @22
    @17
    @3
    cmul
    co
    #
    @23
    @33
    @22
    @34
    wceq
    @19
    @33
    @22
    @16
    cA
    cmul
    co
    #
    ccj
    cfv
    #
    @34
    @33
    @21
    @35
    ccj
    cA
    @15
    expp1
    fveq2d
    @33
    @16
    cc
    wcel
    @0
    @36
    @34
    wceq
    cA
    @15
    expcl
    @0
    @32
    simpl
    @16
    cA
    cjmul
    syl2anc
    eqtrd
    adantr
    @19
    @33
    @34
    @18
    @3
    cmul
    co
    #
    @23
    @17
    @18
    @3
    cmul
    oveq1
    @33
    @23
    @37
    @0
    @30
    @32
    @23
    @37
    wceq
    @31
    @3
    @15
    expp1
    sylan
    eqcomd
    sylan9eqr
    eqtrd
    exp31
    com12
    a2d
    nn0ind
    impcom
end
