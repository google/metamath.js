include "c0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "wcad.mm"
include "c1o.mm"
include "cif.mm"
include "cn0.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "cmin.mm"
include "cmpt.mm"
include "c2o.mm"
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
include "peano2nn0.mm"
include "eqeq1.mm"
include "oveq1.mm"
include "ifbieq2d.mm"
include "eqid.mm"
include "0ex.mm"
include "ovex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "3syl.mm"
include "wne.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "nnne0d.mm"
include "ifnefalse.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "pncand.mm"
include "3eqtrd.mm"
include "oveq2d.mm"
include "sadcf.mm"
include "ffvelrnd.mm"
include "wa.mm"
include "simpr.mm"
include "eleq1d.mm"
include "simpl.mm"
include "eleq2d.mm"
include "cadbi123d.mm"
include "ifbid.mm"
include "biidd.mm"
include "eleq2.mm"
include "eleq1.mm"
include "cbvmpt2v.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "ovmpt2a.mm"
include "syl2anc.mm"
include "wn.mm"
include "noel.mm"
include "iffalse.mm"
include "mtbiri.mm"
include "con4i.mm"
include "0lt1o.mm"
include "iftrue.mm"
include "syl5eleqr.mm"
include "impbii.mm"
include "syl6bb.mm"

theorem sadcp1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let cN: class N
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  assume sadval.a: |- ( ph -> A C_ NN0 )
  assume sadval.b: |- ( ph -> B C_ NN0 )
  assume sadval.c: |- C = seq 0 ( ( c e. 2o , m e. NN0 |-> if ( cadd ( m e. A , m e. B , (/) e. c ) , 1o , (/) ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )
  assume sadcp1.n: |- ( ph -> N e. NN0 )

  disjoint c m
  disjoint c n
  disjoint m n
  disjoint A c
  disjoint A m
  disjoint B c
  disjoint B m
  disjoint N n
  disjoint c k
  disjoint c x
  disjoint c y
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A k
  disjoint A x
  disjoint A y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint C k
  disjoint C x
  disjoint C y
  disjoint K k
  disjoint K x
  disjoint k ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( (/) e. ( C ` ( N + 1 ) ) <-> cadd ( N e. A , N e. B , (/) e. ( C ` N ) ) ) )

  proof
    wph
    c0
    cN
    c1
    caddc
    co
    #
    cC
    cfv
    #
    wcel
    c0
    cN
    cA
    wcel
    #
    cN
    cB
    wcel
    #
    c0
    cN
    cC
    cfv
    #
    wcel
    #
    wcad
    #
    c1o
    c0
    cif
    #
    wcel
    #
    @6
    wph
    @1
    @7
    c0
    wph
    @1
    @4
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
    @9
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
    vc
    vm
    c2o
    cn0
    vm
    cv
    #
    cA
    wcel
    #
    @15
    cB
    wcel
    #
    c0
    vc
    cv
    #
    wcel
    #
    wcad
    #
    c1o
    c0
    cif
    #
    cmpt2
    #
    co
    #
    @4
    cN
    @22
    co
    #
    @7
    wph
    @0
    @22
    @13
    cc0
    cseq
    #
    cfv
    #
    cN
    @25
    cfv
    #
    @14
    @22
    co
    #
    @1
    @23
    wph
    cN
    cc0
    cuz
    cfv
    #
    wcel
    @26
    @28
    wceq
    wph
    cN
    cn0
    @29
    sadcp1.n
    nn0uz
    syl6eleq
    @22
    @13
    cc0
    cN
    seqp1
    syl
    @0
    cC
    @25
    sadval.c
    fveq1i
    @4
    @27
    @14
    @22
    cN
    cC
    @25
    sadval.c
    fveq1i
    oveq1i
    3eqtr4g
    wph
    @14
    cN
    @4
    @22
    wph
    @14
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
    @31
    cN
    wph
    cN
    cn0
    wcel
    #
    @0
    cn0
    wcel
    @14
    @32
    wceq
    sadcp1.n
    cN
    peano2nn0
    vn
    @0
    @12
    @32
    cn0
    @13
    @9
    @0
    wceq
    @10
    @30
    @11
    @31
    c0
    @9
    @0
    cc0
    eqeq1
    @9
    @0
    c1
    cmin
    oveq1
    ifbieq2d
    @13
    eqid
    @30
    c0
    @31
    0ex
    @0
    c1
    cmin
    ovex
    ifex
    fvmpt
    3syl
    wph
    @0
    cc0
    wne
    @32
    @31
    wceq
    wph
    @0
    wph
    @33
    @0
    cn
    wcel
    sadcp1.n
    cN
    nn0p1nn
    syl
    nnne0d
    @0
    cc0
    c0
    @31
    ifnefalse
    syl
    wph
    cN
    c1
    wph
    cN
    sadcp1.n
    nn0cnd
    wph
    1cnd
    pncand
    3eqtrd
    oveq2d
    wph
    @4
    c2o
    wcel
    @33
    @24
    @7
    wceq
    wph
    cn0
    c2o
    cN
    cC
    wph
    cA
    cB
    cC
    vm
    vn
    vc
    sadval.a
    sadval.b
    sadval.c
    sadcf
    sadcp1.n
    ffvelrnd
    sadcp1.n
    vx
    vy
    @4
    cN
    c2o
    cn0
    vy
    cv
    #
    cA
    wcel
    #
    @34
    cB
    wcel
    #
    c0
    vx
    cv
    #
    wcel
    #
    wcad
    #
    c1o
    c0
    cif
    #
    @7
    @22
    @37
    @4
    wceq
    #
    @34
    cN
    wceq
    #
    wa
    #
    @39
    @6
    c1o
    c0
    @43
    @35
    @2
    @36
    @3
    @38
    @5
    @43
    @34
    cN
    cA
    @41
    @42
    simpr
    #
    eleq1d
    @43
    @34
    cN
    cB
    @44
    eleq1d
    @43
    @37
    @4
    c0
    @41
    @42
    simpl
    eleq2d
    cadbi123d
    ifbid
    vc
    vm
    vx
    vy
    c2o
    cn0
    @21
    @40
    @16
    @17
    @38
    wcad
    #
    c1o
    c0
    cif
    @18
    @37
    wceq
    #
    @20
    @45
    c1o
    c0
    @46
    @16
    @16
    @17
    @17
    @19
    @38
    @46
    @16
    biidd
    @46
    @17
    biidd
    @18
    @37
    c0
    eleq2
    cadbi123d
    ifbid
    @15
    @34
    wceq
    #
    @45
    @39
    c1o
    c0
    @47
    @16
    @35
    @17
    @36
    @38
    @38
    @15
    @34
    cA
    eleq1
    @15
    @34
    cB
    eleq1
    @47
    @38
    biidd
    cadbi123d
    ifbid
    cbvmpt2v
    @6
    c1o
    c0
    c1o
    con0
    1on
    elexi
    0ex
    ifex
    ovmpt2a
    syl2anc
    3eqtrd
    eleq2d
    @8
    @6
    @6
    @8
    @6
    wn
    #
    @8
    c0
    c0
    wcel
    c0
    noel
    @48
    @7
    c0
    c0
    @6
    c1o
    c0
    iffalse
    eleq2d
    mtbiri
    con4i
    @6
    c0
    c1o
    @7
    0lt1o
    @6
    c1o
    c0
    iftrue
    syl5eleqr
    impbii
    syl6bb
end
