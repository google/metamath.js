include "cn0.mm"
include "wcel.mm"
include "csad.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "cin.mm"
include "cfv.mm"
include "c0.mm"
include "c2.mm"
include "cexp.mm"
include "cif.mm"
include "caddc.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "oveq2.mm"
include "fzo0.mm"
include "syl6eq.mm"
include "ineq2d.mm"
include "in0.mm"
include "fveq2d.mm"
include "cbits.mm"
include "cres.mm"
include "ccnv.mm"
include "0nn0.mm"
include "fvres.mm"
include "ax-mp.mm"
include "0bits.mm"
include "eqtr2i.mm"
include "fveq12i.mm"
include "cpw.mm"
include "cfn.mm"
include "wf1o.mm"
include "bitsf1o.mm"
include "f1ocnvfv1.mm"
include "mp2an.mm"
include "eqtri.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "ifbieq1d.mm"
include "oveq12d.mm"
include "00id.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "sadc0.mm"
include "iffalsed.mm"
include "oveq2d.mm"
include "wa.mm"
include "wss.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "sadadd2lem.mm"
include "ex.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "mpcom.mm"

theorem sadadd2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let cK: class K
  let cN: class N
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume sadval.a: |- ( ph -> A C_ NN0 )
  assume sadval.b: |- ( ph -> B C_ NN0 )
  assume sadval.c: |- C = seq 0 ( ( c e. 2o , m e. NN0 |-> if ( cadd ( m e. A , m e. B , (/) e. c ) , 1o , (/) ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )
  assume sadcp1.n: |- ( ph -> N e. NN0 )
  assume sadcadd.k: |- K = `' ( bits |` NN0 )

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
  assert |- ( ph -> ( ( K ` ( ( A sadd B ) i^i ( 0 ..^ N ) ) ) + if ( (/) e. ( C ` N ) , ( 2 ^ N ) , 0 ) ) = ( ( K ` ( A i^i ( 0 ..^ N ) ) ) + ( K ` ( B i^i ( 0 ..^ N ) ) ) ) )

  proof
    cN
    cn0
    wcel
    wph
    cA
    cB
    csad
    co
    #
    cc0
    cN
    cfzo
    co
    #
    cin
    #
    cK
    cfv
    #
    c0
    cN
    cC
    cfv
    #
    wcel
    #
    c2
    cN
    cexp
    co
    #
    cc0
    cif
    #
    caddc
    co
    #
    cA
    @1
    cin
    #
    cK
    cfv
    #
    cB
    @1
    cin
    #
    cK
    cfv
    #
    caddc
    co
    #
    wceq
    #
    sadcp1.n
    wph
    @0
    cc0
    vx
    cv
    #
    cfzo
    co
    #
    cin
    #
    cK
    cfv
    #
    c0
    @15
    cC
    cfv
    #
    wcel
    #
    c2
    @15
    cexp
    co
    #
    cc0
    cif
    #
    caddc
    co
    #
    cA
    @16
    cin
    #
    cK
    cfv
    #
    cB
    @16
    cin
    #
    cK
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    wph
    cc0
    c0
    cc0
    cC
    cfv
    #
    wcel
    #
    c2
    cc0
    cexp
    co
    #
    cc0
    cif
    #
    caddc
    co
    #
    cc0
    wceq
    #
    wi
    wph
    @0
    cc0
    vk
    cv
    #
    cfzo
    co
    #
    cin
    #
    cK
    cfv
    #
    c0
    @36
    cC
    cfv
    #
    wcel
    #
    c2
    @36
    cexp
    co
    #
    cc0
    cif
    #
    caddc
    co
    #
    cA
    @37
    cin
    #
    cK
    cfv
    #
    cB
    @37
    cin
    #
    cK
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    wph
    @0
    cc0
    @36
    c1
    caddc
    co
    #
    cfzo
    co
    #
    cin
    #
    cK
    cfv
    #
    c0
    @51
    cC
    cfv
    #
    wcel
    #
    c2
    @51
    cexp
    co
    #
    cc0
    cif
    #
    caddc
    co
    #
    cA
    @52
    cin
    #
    cK
    cfv
    #
    cB
    @52
    cin
    #
    cK
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    wph
    @14
    wi
    vx
    vk
    cN
    @15
    cc0
    wceq
    #
    @29
    @35
    wph
    @66
    @23
    @34
    @28
    cc0
    @66
    @18
    cc0
    @22
    @33
    caddc
    @66
    @18
    c0
    cK
    cfv
    #
    cc0
    @66
    @17
    c0
    cK
    @66
    @17
    @0
    c0
    cin
    c0
    @66
    @16
    c0
    @0
    @66
    @16
    cc0
    cc0
    cfzo
    co
    c0
    @15
    cc0
    cc0
    cfzo
    oveq2
    cc0
    fzo0
    syl6eq
    #
    ineq2d
    @0
    in0
    syl6eq
    fveq2d
    @67
    cc0
    cbits
    cn0
    cres
    #
    cfv
    #
    @69
    ccnv
    #
    cfv
    #
    cc0
    c0
    @70
    cK
    @71
    sadcadd.k
    @70
    cc0
    cbits
    cfv
    #
    c0
    cc0
    cn0
    wcel
    #
    @70
    @73
    wceq
    0nn0
    cc0
    cn0
    cbits
    fvres
    ax-mp
    0bits
    eqtr2i
    fveq12i
    cn0
    cn0
    cpw
    cfn
    cin
    #
    @69
    wf1o
    @74
    @72
    cc0
    wceq
    bitsf1o
    0nn0
    cn0
    @75
    cc0
    @69
    f1ocnvfv1
    mp2an
    eqtri
    #
    syl6eq
    @66
    @20
    @31
    @21
    @32
    cc0
    @66
    @19
    @30
    c0
    @15
    cc0
    cC
    fveq2
    eleq2d
    @15
    cc0
    c2
    cexp
    oveq2
    ifbieq1d
    oveq12d
    @66
    @28
    cc0
    cc0
    caddc
    co
    #
    cc0
    @66
    @25
    cc0
    @27
    cc0
    caddc
    @66
    @25
    @67
    cc0
    @66
    @24
    c0
    cK
    @66
    @24
    cA
    c0
    cin
    c0
    @66
    @16
    c0
    cA
    @68
    ineq2d
    cA
    in0
    syl6eq
    fveq2d
    @76
    syl6eq
    @66
    @27
    @67
    cc0
    @66
    @26
    c0
    cK
    @66
    @26
    cB
    c0
    cin
    c0
    @66
    @16
    c0
    cB
    @68
    ineq2d
    cB
    in0
    syl6eq
    fveq2d
    @76
    syl6eq
    oveq12d
    00id
    syl6eq
    eqeq12d
    imbi2d
    @15
    @36
    wceq
    #
    @29
    @50
    wph
    @78
    @23
    @44
    @28
    @49
    @78
    @18
    @39
    @22
    @43
    caddc
    @78
    @17
    @38
    cK
    @78
    @16
    @37
    @0
    @15
    @36
    cc0
    cfzo
    oveq2
    #
    ineq2d
    fveq2d
    @78
    @20
    @41
    @21
    @42
    cc0
    @78
    @19
    @40
    c0
    @15
    @36
    cC
    fveq2
    eleq2d
    @15
    @36
    c2
    cexp
    oveq2
    ifbieq1d
    oveq12d
    @78
    @25
    @46
    @27
    @48
    caddc
    @78
    @24
    @45
    cK
    @78
    @16
    @37
    cA
    @79
    ineq2d
    fveq2d
    @78
    @26
    @47
    cK
    @78
    @16
    @37
    cB
    @79
    ineq2d
    fveq2d
    oveq12d
    eqeq12d
    imbi2d
    @15
    @51
    wceq
    #
    @29
    @65
    wph
    @80
    @23
    @59
    @28
    @64
    @80
    @18
    @54
    @22
    @58
    caddc
    @80
    @17
    @53
    cK
    @80
    @16
    @52
    @0
    @15
    @51
    cc0
    cfzo
    oveq2
    #
    ineq2d
    fveq2d
    @80
    @20
    @56
    @21
    @57
    cc0
    @80
    @19
    @55
    c0
    @15
    @51
    cC
    fveq2
    eleq2d
    @15
    @51
    c2
    cexp
    oveq2
    ifbieq1d
    oveq12d
    @80
    @25
    @61
    @27
    @63
    caddc
    @80
    @24
    @60
    cK
    @80
    @16
    @52
    cA
    @81
    ineq2d
    fveq2d
    @80
    @26
    @62
    cK
    @80
    @16
    @52
    cB
    @81
    ineq2d
    fveq2d
    oveq12d
    eqeq12d
    imbi2d
    @15
    cN
    wceq
    #
    @29
    @14
    wph
    @82
    @23
    @8
    @28
    @13
    @82
    @18
    @3
    @22
    @7
    caddc
    @82
    @17
    @2
    cK
    @82
    @16
    @1
    @0
    @15
    cN
    cc0
    cfzo
    oveq2
    #
    ineq2d
    fveq2d
    @82
    @20
    @5
    @21
    @6
    cc0
    @82
    @19
    @4
    c0
    @15
    cN
    cC
    fveq2
    eleq2d
    @15
    cN
    c2
    cexp
    oveq2
    ifbieq1d
    oveq12d
    @82
    @25
    @10
    @27
    @12
    caddc
    @82
    @24
    @9
    cK
    @82
    @16
    @1
    cA
    @83
    ineq2d
    fveq2d
    @82
    @26
    @11
    cK
    @82
    @16
    @1
    cB
    @83
    ineq2d
    fveq2d
    oveq12d
    eqeq12d
    imbi2d
    wph
    @34
    @77
    cc0
    wph
    @33
    cc0
    cc0
    caddc
    wph
    @31
    @32
    cc0
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
    sadc0
    iffalsed
    oveq2d
    00id
    syl6eq
    @36
    cn0
    wcel
    #
    wph
    @50
    @65
    wph
    @84
    @50
    @65
    wi
    wph
    @84
    wa
    #
    @50
    @65
    @85
    @50
    wa
    cA
    cB
    cC
    vm
    vn
    cK
    @36
    vc
    wph
    cA
    cn0
    wss
    @84
    @50
    sadval.a
    ad2antrr
    wph
    cB
    cn0
    wss
    @84
    @50
    sadval.b
    ad2antrr
    sadval.c
    wph
    @84
    @50
    simplr
    sadcadd.k
    @85
    @50
    simpr
    sadadd2lem
    ex
    expcom
    a2d
    nn0ind
    mpcom
end
