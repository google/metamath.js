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
include "oveq12d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "mulcl.mm"
include "exp0.mm"
include "syl.mm"
include "oveqan12d.mm"
include "1t1e1.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "expp1.mm"
include "sylan.mm"
include "adantr.mm"
include "oveq1.mm"
include "expcl.mm"
include "anim12i.mm"
include "anandirs.mm"
include "simpl.mm"
include "mul4.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "adantll.mm"
include "sylan9eqr.mm"
include "eqtrd.mm"
include "exp31.mm"
include "com12.mm"
include "a2d.mm"
include "nn0ind.mm"
include "expdcom.mm"
include "3imp.mm"

theorem mulexp
  let cA: class A
  let cB: class B
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  let cM: class M


  assert |- ( ( A e. CC /\ B e. CC /\ N e. NN0 ) -> ( ( A x. B ) ^ N ) = ( ( A ^ N ) x. ( B ^ N ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cN
    cn0
    wcel
    #
    cA
    cB
    cmul
    co
    #
    cN
    cexp
    co
    #
    cA
    cN
    cexp
    co
    #
    cB
    cN
    cexp
    co
    #
    cmul
    co
    #
    wceq
    #
    @2
    @0
    @1
    @8
    @0
    @1
    wa
    #
    @3
    vj
    cv
    #
    cexp
    co
    #
    cA
    @10
    cexp
    co
    #
    cB
    @10
    cexp
    co
    #
    cmul
    co
    #
    wceq
    #
    wi
    @9
    @3
    cc0
    cexp
    co
    #
    cA
    cc0
    cexp
    co
    #
    cB
    cc0
    cexp
    co
    #
    cmul
    co
    #
    wceq
    #
    wi
    @9
    @3
    vk
    cv
    #
    cexp
    co
    #
    cA
    @21
    cexp
    co
    #
    cB
    @21
    cexp
    co
    #
    cmul
    co
    #
    wceq
    #
    wi
    @9
    @3
    @21
    c1
    caddc
    co
    #
    cexp
    co
    #
    cA
    @27
    cexp
    co
    #
    cB
    @27
    cexp
    co
    #
    cmul
    co
    #
    wceq
    #
    wi
    @9
    @8
    wi
    vj
    vk
    cN
    @10
    cc0
    wceq
    #
    @15
    @20
    @9
    @33
    @11
    @16
    @14
    @19
    @10
    cc0
    @3
    cexp
    oveq2
    @33
    @12
    @17
    @13
    @18
    cmul
    @10
    cc0
    cA
    cexp
    oveq2
    @10
    cc0
    cB
    cexp
    oveq2
    oveq12d
    eqeq12d
    imbi2d
    @10
    @21
    wceq
    #
    @15
    @26
    @9
    @34
    @11
    @22
    @14
    @25
    @10
    @21
    @3
    cexp
    oveq2
    @34
    @12
    @23
    @13
    @24
    cmul
    @10
    @21
    cA
    cexp
    oveq2
    @10
    @21
    cB
    cexp
    oveq2
    oveq12d
    eqeq12d
    imbi2d
    @10
    @27
    wceq
    #
    @15
    @32
    @9
    @35
    @11
    @28
    @14
    @31
    @10
    @27
    @3
    cexp
    oveq2
    @35
    @12
    @29
    @13
    @30
    cmul
    @10
    @27
    cA
    cexp
    oveq2
    @10
    @27
    cB
    cexp
    oveq2
    oveq12d
    eqeq12d
    imbi2d
    @10
    cN
    wceq
    #
    @15
    @8
    @9
    @36
    @11
    @4
    @14
    @7
    @10
    cN
    @3
    cexp
    oveq2
    @36
    @12
    @5
    @13
    @6
    cmul
    @10
    cN
    cA
    cexp
    oveq2
    @10
    cN
    cB
    cexp
    oveq2
    oveq12d
    eqeq12d
    imbi2d
    @9
    @16
    c1
    @19
    @9
    @3
    cc
    wcel
    #
    @16
    c1
    wceq
    cA
    cB
    mulcl
    #
    @3
    exp0
    syl
    @9
    @19
    c1
    c1
    cmul
    co
    c1
    @0
    @1
    @17
    c1
    @18
    c1
    cmul
    cA
    exp0
    cB
    exp0
    oveqan12d
    1t1e1
    syl6eq
    eqtr4d
    @21
    cn0
    wcel
    #
    @9
    @26
    @32
    @9
    @39
    @26
    @32
    wi
    @9
    @39
    @26
    @32
    @9
    @39
    wa
    #
    @26
    wa
    @28
    @22
    @3
    cmul
    co
    #
    @31
    @40
    @28
    @41
    wceq
    #
    @26
    @9
    @37
    @39
    @42
    @38
    @3
    @21
    expp1
    sylan
    adantr
    @26
    @40
    @41
    @25
    @3
    cmul
    co
    #
    @31
    @22
    @25
    @3
    cmul
    oveq1
    @40
    @43
    @23
    cA
    cmul
    co
    #
    @24
    cB
    cmul
    co
    #
    cmul
    co
    #
    @31
    @40
    @23
    cc
    wcel
    #
    @24
    cc
    wcel
    #
    wa
    #
    @9
    @43
    @46
    wceq
    @0
    @1
    @39
    @49
    @0
    @39
    wa
    @47
    @1
    @39
    wa
    @48
    cA
    @21
    expcl
    cB
    @21
    expcl
    anim12i
    anandirs
    @9
    @39
    simpl
    @23
    @24
    cA
    cB
    mul4
    syl2anc
    @40
    @29
    @44
    @30
    @45
    cmul
    @0
    @39
    @29
    @44
    wceq
    @1
    cA
    @21
    expp1
    adantlr
    @1
    @39
    @30
    @45
    wceq
    @0
    cB
    @21
    expp1
    adantll
    oveq12d
    eqtr4d
    sylan9eqr
    eqtrd
    exp31
    com12
    a2d
    nn0ind
    expdcom
    3imp
end
