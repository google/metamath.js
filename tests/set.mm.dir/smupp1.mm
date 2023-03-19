include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "c0.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "cpw.mm"
include "wcel.mm"
include "wa.mm"
include "crab.mm"
include "csad.mm"
include "cmpt2.mm"
include "cseq.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "seqp1.mm"
include "syl.mm"
include "fveq1i.mm"
include "oveq1i.mm"
include "3eqtr4g.mm"
include "1nn0.mm"
include "a1i.mm"
include "nn0addcld.mm"
include "eqeq1.mm"
include "oveq1.mm"
include "ifbieq2d.mm"
include "eqid.mm"
include "0ex.mm"
include "ovex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "wne.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "nnne0d.mm"
include "ifnefalse.mm"
include "nn0cnd.mm"
include "pncand.mm"
include "3eqtrd.mm"
include "oveq2d.mm"
include "smupf.mm"
include "ffvelrnd.mm"
include "simpl.mm"
include "simpr.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rabbidv.mm"
include "anbi2d.mm"
include "cbvrabv.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "eleq1.mm"
include "oveq2.mm"
include "syl6eqr.mm"
include "cbvmpt2v.mm"
include "ovmpt2a.mm"
include "syl2anc.mm"

theorem smupp1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let vm: setvar m
  let vn: setvar n
  let cN: class N
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  assume smuval.a: |- ( ph -> A C_ NN0 )
  assume smuval.b: |- ( ph -> B C_ NN0 )
  assume smuval.p: |- P = seq 0 ( ( p e. ~P NN0 , m e. NN0 |-> ( p sadd { n e. NN0 | ( m e. A /\ ( n - m ) e. B ) } ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )
  assume smuval.n: |- ( ph -> N e. NN0 )

  disjoint m n
  disjoint m p
  disjoint A m
  disjoint n p
  disjoint A n
  disjoint A p
  disjoint N n
  disjoint n ph
  disjoint B m
  disjoint B n
  disjoint B p
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint p x
  disjoint p y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint M k
  disjoint M x
  disjoint P k
  disjoint P x
  disjoint P y
  assert |- ( ph -> ( P ` ( N + 1 ) ) = ( ( P ` N ) sadd { n e. NN0 | ( N e. A /\ ( n - N ) e. B ) } ) )

  proof
    wph
    cN
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cN
    cP
    cfv
    #
    @0
    vn
    cn0
    vn
    cv
    #
    cc0
    wceq
    #
    c0
    @3
    c1
    cmin
    co
    #
    cif
    #
    cmpt
    #
    cfv
    #
    vp
    vm
    cn0
    cpw
    #
    cn0
    vp
    cv
    #
    vm
    cv
    #
    cA
    wcel
    #
    @3
    @11
    cmin
    co
    #
    cB
    wcel
    #
    wa
    #
    vn
    cn0
    crab
    #
    csad
    co
    #
    cmpt2
    #
    co
    #
    @2
    cN
    @18
    co
    #
    @2
    cN
    cA
    wcel
    #
    @3
    cN
    cmin
    co
    #
    cB
    wcel
    #
    wa
    #
    vn
    cn0
    crab
    #
    csad
    co
    #
    wph
    @0
    @18
    @7
    cc0
    cseq
    #
    cfv
    #
    cN
    @27
    cfv
    #
    @8
    @18
    co
    #
    @1
    @19
    wph
    cN
    cc0
    cuz
    cfv
    #
    wcel
    @28
    @30
    wceq
    wph
    cN
    cn0
    @31
    smuval.n
    nn0uz
    syl6eleq
    @18
    @7
    cc0
    cN
    seqp1
    syl
    @0
    cP
    @27
    smuval.p
    fveq1i
    @2
    @29
    @8
    @18
    cN
    cP
    @27
    smuval.p
    fveq1i
    oveq1i
    3eqtr4g
    wph
    @8
    cN
    @2
    @18
    wph
    @8
    @0
    cc0
    wceq
    #
    c0
    @0
    c1
    cmin
    co
    #
    cif
    #
    @33
    cN
    wph
    @0
    cn0
    wcel
    @8
    @34
    wceq
    wph
    cN
    c1
    smuval.n
    c1
    cn0
    wcel
    wph
    1nn0
    a1i
    #
    nn0addcld
    vn
    @0
    @6
    @34
    cn0
    @7
    @3
    @0
    wceq
    @4
    @32
    @5
    @33
    c0
    @3
    @0
    cc0
    eqeq1
    @3
    @0
    c1
    cmin
    oveq1
    ifbieq2d
    @7
    eqid
    @32
    c0
    @33
    0ex
    @0
    c1
    cmin
    ovex
    ifex
    fvmpt
    syl
    wph
    @0
    cc0
    wne
    @34
    @33
    wceq
    wph
    @0
    wph
    cN
    cn0
    wcel
    #
    @0
    cn
    wcel
    smuval.n
    cN
    nn0p1nn
    syl
    nnne0d
    @0
    cc0
    c0
    @33
    ifnefalse
    syl
    wph
    cN
    c1
    wph
    cN
    smuval.n
    nn0cnd
    wph
    c1
    @35
    nn0cnd
    pncand
    3eqtrd
    oveq2d
    wph
    @2
    @9
    wcel
    @36
    @20
    @26
    wceq
    wph
    cn0
    @9
    cN
    cP
    wph
    cA
    cB
    cP
    vm
    vn
    vp
    smuval.a
    smuval.b
    smuval.p
    smupf
    smuval.n
    ffvelrnd
    smuval.n
    vx
    vy
    @2
    cN
    @9
    cn0
    vx
    cv
    #
    vy
    cv
    #
    cA
    wcel
    #
    vk
    cv
    #
    @38
    cmin
    co
    #
    cB
    wcel
    #
    wa
    #
    vk
    cn0
    crab
    #
    csad
    co
    #
    @26
    @18
    @37
    @2
    wceq
    #
    @38
    cN
    wceq
    #
    wa
    #
    @37
    @2
    @44
    @25
    csad
    @46
    @47
    simpl
    @48
    @44
    @21
    @40
    cN
    cmin
    co
    #
    cB
    wcel
    #
    wa
    #
    vk
    cn0
    crab
    @25
    @48
    @43
    @51
    vk
    cn0
    @48
    @39
    @21
    @42
    @50
    @48
    @38
    cN
    cA
    @46
    @47
    simpr
    #
    eleq1d
    @48
    @41
    @49
    cB
    @48
    @38
    cN
    @40
    cmin
    @52
    oveq2d
    eleq1d
    anbi12d
    rabbidv
    @51
    @24
    vk
    vn
    cn0
    @40
    @3
    wceq
    #
    @50
    @23
    @21
    @53
    @49
    @22
    cB
    @40
    @3
    cN
    cmin
    oveq1
    eleq1d
    anbi2d
    cbvrabv
    syl6eq
    oveq12d
    vp
    vm
    vx
    vy
    @9
    cn0
    @17
    @45
    @37
    @16
    csad
    co
    @10
    @37
    @16
    csad
    oveq1
    @11
    @38
    wceq
    #
    @16
    @44
    @37
    csad
    @54
    @16
    @39
    @3
    @38
    cmin
    co
    #
    cB
    wcel
    #
    wa
    #
    vn
    cn0
    crab
    @44
    @54
    @15
    @57
    vn
    cn0
    @54
    @12
    @39
    @14
    @56
    @11
    @38
    cA
    eleq1
    @54
    @13
    @55
    cB
    @11
    @38
    @3
    cmin
    oveq2
    eleq1d
    anbi12d
    rabbidv
    @43
    @57
    vk
    vn
    cn0
    @53
    @42
    @56
    @39
    @53
    @41
    @55
    cB
    @40
    @3
    @38
    cmin
    oveq1
    eleq1d
    anbi2d
    cbvrabv
    syl6eqr
    oveq2d
    cbvmpt2v
    @2
    @25
    csad
    ovex
    ovmpt2a
    syl2anc
    3eqtrd
end
