include "cn0.mm"
include "cpw.mm"
include "wcel.mm"
include "csad.mm"
include "co.mm"
include "cv.mm"
include "c0.mm"
include "cfv.mm"
include "whad.mm"
include "crab.mm"
include "wceq.mm"
include "wss.mm"
include "nn0ex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "c2o.mm"
include "wcad.mm"
include "c1o.mm"
include "cif.mm"
include "cmpt2.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "cmpt.mm"
include "cseq.mm"
include "wa.mm"
include "simpl.mm"
include "eleq2d.mm"
include "simpr.mm"
include "w3a.mm"
include "simp1l.mm"
include "simp1r.mm"
include "biidd.mm"
include "cadbi123d.mm"
include "ifbid.mm"
include "mpt2eq3dva.mm"
include "seqeq2d.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "hadbi123d.mm"
include "rabbidv.mm"
include "df-sad.mm"
include "rabex.mm"
include "ovmpt2a.mm"
include "syl2anc.mm"

theorem sadfval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  let cK: class K
  assume sadval.a: |- ( ph -> A C_ NN0 )
  assume sadval.b: |- ( ph -> B C_ NN0 )
  assume sadval.c: |- C = seq 0 ( ( c e. 2o , m e. NN0 |-> if ( cadd ( m e. A , m e. B , (/) e. c ) , 1o , (/) ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )

  disjoint c k
  disjoint c m
  disjoint c n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint A c
  disjoint A k
  disjoint A m
  disjoint B c
  disjoint B k
  disjoint B m
  disjoint C k
  disjoint k ph
  disjoint c x
  disjoint c y
  disjoint k x
  disjoint k y
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint N k
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint C x
  disjoint C y
  disjoint K k
  disjoint K x
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( A sadd B ) = { k e. NN0 | hadd ( k e. A , k e. B , (/) e. ( C ` k ) ) } )

  proof
    wph
    cA
    cn0
    cpw
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cA
    cB
    csad
    co
    vk
    cv
    #
    cA
    wcel
    #
    @3
    cB
    wcel
    #
    c0
    @3
    cC
    cfv
    #
    wcel
    #
    whad
    #
    vk
    cn0
    crab
    #
    wceq
    wph
    cA
    cn0
    wss
    @1
    sadval.a
    cA
    cn0
    nn0ex
    elpw2
    sylibr
    wph
    cB
    cn0
    wss
    @2
    sadval.b
    cB
    cn0
    nn0ex
    elpw2
    sylibr
    vx
    vy
    cA
    cB
    @0
    @0
    @3
    vx
    cv
    #
    wcel
    #
    @3
    vy
    cv
    #
    wcel
    #
    c0
    @3
    vc
    vm
    c2o
    cn0
    vm
    cv
    #
    @10
    wcel
    #
    @14
    @12
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
    vn
    cn0
    vn
    cv
    #
    cc0
    wceq
    c0
    @22
    c1
    cmin
    co
    cif
    cmpt
    #
    cc0
    cseq
    #
    cfv
    #
    wcel
    #
    whad
    #
    vk
    cn0
    crab
    @9
    csad
    @10
    cA
    wceq
    #
    @12
    cB
    wceq
    #
    wa
    #
    @27
    @8
    vk
    cn0
    @30
    @11
    @4
    @13
    @5
    @26
    @7
    @30
    @10
    cA
    @3
    @28
    @29
    simpl
    eleq2d
    @30
    @12
    cB
    @3
    @28
    @29
    simpr
    eleq2d
    @30
    @25
    @6
    c0
    @30
    @3
    @24
    cC
    @30
    @24
    vc
    vm
    c2o
    cn0
    @14
    cA
    wcel
    #
    @14
    cB
    wcel
    #
    @18
    wcad
    #
    c1o
    c0
    cif
    #
    cmpt2
    #
    @23
    cc0
    cseq
    cC
    @30
    @21
    @35
    @23
    cc0
    @30
    vc
    vm
    c2o
    cn0
    @20
    @34
    @30
    @17
    c2o
    wcel
    #
    @14
    cn0
    wcel
    #
    w3a
    #
    @19
    @33
    c1o
    c0
    @38
    @15
    @31
    @16
    @32
    @18
    @18
    @38
    @10
    cA
    @14
    @28
    @29
    @36
    @37
    simp1l
    eleq2d
    @38
    @12
    cB
    @14
    @28
    @29
    @36
    @37
    simp1r
    eleq2d
    @38
    @18
    biidd
    cadbi123d
    ifbid
    mpt2eq3dva
    seqeq2d
    sadval.c
    syl6eqr
    fveq1d
    eleq2d
    hadbi123d
    rabbidv
    vx
    vy
    vk
    vm
    vn
    vc
    df-sad
    @8
    vk
    cn0
    nn0ex
    rabex
    ovmpt2a
    syl2anc
end
