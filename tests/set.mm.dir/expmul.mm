include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "cmul.mm"
include "co.mm"
include "cexp.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "nn0cn.mm"
include "mul01d.mm"
include "exp0.mm"
include "sylan9eqr.mm"
include "expcl.mm"
include "syl.mm"
include "eqtr4d.mm"
include "oveq1.mm"
include "ax-1cn.mm"
include "adddi.mm"
include "mp3an3.mm"
include "mulid1.mm"
include "adantr.mm"
include "eqtrd.mm"
include "syl2an.mm"
include "adantll.mm"
include "simpll.mm"
include "nn0mulcl.mm"
include "simplr.mm"
include "expadd.mm"
include "syl3anc.mm"
include "expp1.mm"
include "sylan.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "expdcom.mm"
include "3imp.mm"

theorem expmul
  let cA: class A
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  let cB: class B


  assert |- ( ( A e. CC /\ M e. NN0 /\ N e. NN0 ) -> ( A ^ ( M x. N ) ) = ( ( A ^ M ) ^ N ) )

  proof
    cA
    cc
    wcel
    #
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    cA
    cM
    cN
    cmul
    co
    #
    cexp
    co
    #
    cA
    cM
    cexp
    co
    #
    cN
    cexp
    co
    #
    wceq
    #
    @2
    @0
    @1
    @7
    @0
    @1
    wa
    #
    cA
    cM
    vj
    cv
    #
    cmul
    co
    #
    cexp
    co
    #
    @5
    @9
    cexp
    co
    #
    wceq
    #
    wi
    @8
    cA
    cM
    cc0
    cmul
    co
    #
    cexp
    co
    #
    @5
    cc0
    cexp
    co
    #
    wceq
    #
    wi
    @8
    cA
    cM
    vk
    cv
    #
    cmul
    co
    #
    cexp
    co
    #
    @5
    @18
    cexp
    co
    #
    wceq
    #
    wi
    @8
    cA
    cM
    @18
    c1
    caddc
    co
    #
    cmul
    co
    #
    cexp
    co
    #
    @5
    @23
    cexp
    co
    #
    wceq
    #
    wi
    @8
    @7
    wi
    vj
    vk
    cN
    @9
    cc0
    wceq
    #
    @13
    @17
    @8
    @28
    @11
    @15
    @12
    @16
    @28
    @10
    @14
    cA
    cexp
    @9
    cc0
    cM
    cmul
    oveq2
    oveq2d
    @9
    cc0
    @5
    cexp
    oveq2
    eqeq12d
    imbi2d
    @9
    @18
    wceq
    #
    @13
    @22
    @8
    @29
    @11
    @20
    @12
    @21
    @29
    @10
    @19
    cA
    cexp
    @9
    @18
    cM
    cmul
    oveq2
    oveq2d
    @9
    @18
    @5
    cexp
    oveq2
    eqeq12d
    imbi2d
    @9
    @23
    wceq
    #
    @13
    @27
    @8
    @30
    @11
    @25
    @12
    @26
    @30
    @10
    @24
    cA
    cexp
    @9
    @23
    cM
    cmul
    oveq2
    oveq2d
    @9
    @23
    @5
    cexp
    oveq2
    eqeq12d
    imbi2d
    @9
    cN
    wceq
    #
    @13
    @7
    @8
    @31
    @11
    @4
    @12
    @6
    @31
    @10
    @3
    cA
    cexp
    @9
    cN
    cM
    cmul
    oveq2
    oveq2d
    @9
    cN
    @5
    cexp
    oveq2
    eqeq12d
    imbi2d
    @8
    @15
    c1
    @16
    @1
    @0
    @15
    cA
    cc0
    cexp
    co
    c1
    @1
    @14
    cc0
    cA
    cexp
    @1
    cM
    cM
    nn0cn
    #
    mul01d
    oveq2d
    cA
    exp0
    sylan9eqr
    @8
    @5
    cc
    wcel
    #
    @16
    c1
    wceq
    cA
    cM
    expcl
    #
    @5
    exp0
    syl
    eqtr4d
    @18
    cn0
    wcel
    #
    @8
    @22
    @27
    @8
    @35
    @22
    @27
    wi
    @22
    @27
    @8
    @35
    wa
    #
    @20
    @5
    cmul
    co
    #
    @21
    @5
    cmul
    co
    #
    wceq
    @20
    @21
    @5
    cmul
    oveq1
    @36
    @25
    @37
    @26
    @38
    @36
    @25
    cA
    @19
    cM
    caddc
    co
    #
    cexp
    co
    #
    @37
    @36
    @24
    @39
    cA
    cexp
    @1
    @35
    @24
    @39
    wceq
    #
    @0
    @1
    cM
    cc
    wcel
    #
    @18
    cc
    wcel
    #
    @41
    @35
    @32
    @18
    nn0cn
    @42
    @43
    wa
    #
    @24
    @19
    cM
    c1
    cmul
    co
    #
    caddc
    co
    #
    @39
    @42
    @43
    c1
    cc
    wcel
    @24
    @46
    wceq
    ax-1cn
    cM
    @18
    c1
    adddi
    mp3an3
    @44
    @45
    cM
    @19
    caddc
    @42
    @45
    cM
    wceq
    @43
    cM
    mulid1
    adantr
    oveq2d
    eqtrd
    syl2an
    adantll
    oveq2d
    @36
    @0
    @19
    cn0
    wcel
    #
    @1
    @40
    @37
    wceq
    @0
    @1
    @35
    simpll
    @1
    @35
    @47
    @0
    cM
    @18
    nn0mulcl
    adantll
    @0
    @1
    @35
    simplr
    cA
    @19
    cM
    expadd
    syl3anc
    eqtrd
    @8
    @33
    @35
    @26
    @38
    wceq
    @34
    @5
    @18
    expp1
    sylan
    eqeq12d
    syl5ibr
    expcom
    a2d
    nn0ind
    expdcom
    3imp
end
