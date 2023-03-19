include "csad.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "cin.mm"
include "cfv.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "cif.mm"
include "caddc.mm"
include "c0.mm"
include "c1.mm"
include "cn0.mm"
include "cpw.mm"
include "cfn.mm"
include "wss.mm"
include "inss1.mm"
include "cv.mm"
include "whad.mm"
include "crab.mm"
include "sadfval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "syl5ss.mm"
include "fzofi.mm"
include "a1i.mm"
include "inss2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "elfpw.mm"
include "sylanbrc.mm"
include "wf.mm"
include "cbits.mm"
include "cres.mm"
include "ccnv.mm"
include "wf1o.mm"
include "bitsf1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "mp2b.mm"
include "feq1i.mm"
include "mpbir.mm"
include "ffvelrni.mm"
include "syl.mm"
include "nn0cnd.mm"
include "2nn0.mm"
include "nn0expcld.mm"
include "0nn0.mm"
include "ifcl.mm"
include "1nn0.mm"
include "nn0addcld.mm"
include "addcld.mm"
include "cc.mm"
include "adantr.mm"
include "wn.mm"
include "wa.mm"
include "0cnd.mm"
include "ifclda.mm"
include "wcad.mm"
include "cmul.mm"
include "sadval.mm"
include "ifbid.mm"
include "sadcp1.mm"
include "expp1d.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "ifbieq1d.mm"
include "oveq12d.mm"
include "wceq.mm"
include "sadadd2lem2.mm"
include "add32d.mm"
include "addassd.mm"
include "3eqtr4d.mm"
include "addcan2ad.mm"
include "add4d.mm"
include "bitsinvp1.mm"
include "syl2anc.mm"
include "oveq1d.mm"

theorem sadadd2lem
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
  assume sadadd2lem.1: |- ( ph -> ( ( K ` ( ( A sadd B ) i^i ( 0 ..^ N ) ) ) + if ( (/) e. ( C ` N ) , ( 2 ^ N ) , 0 ) ) = ( ( K ` ( A i^i ( 0 ..^ N ) ) ) + ( K ` ( B i^i ( 0 ..^ N ) ) ) ) )

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
  assert |- ( ph -> ( ( K ` ( ( A sadd B ) i^i ( 0 ..^ ( N + 1 ) ) ) ) + if ( (/) e. ( C ` ( N + 1 ) ) , ( 2 ^ ( N + 1 ) ) , 0 ) ) = ( ( K ` ( A i^i ( 0 ..^ ( N + 1 ) ) ) ) + ( K ` ( B i^i ( 0 ..^ ( N + 1 ) ) ) ) ) )

  proof
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
    cN
    @0
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
    c0
    cN
    c1
    caddc
    co
    #
    cC
    cfv
    wcel
    #
    c2
    @8
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
    cN
    cA
    wcel
    #
    @5
    cc0
    cif
    #
    caddc
    co
    #
    cB
    @1
    cin
    #
    cK
    cfv
    #
    cN
    cB
    wcel
    #
    @5
    cc0
    cif
    #
    caddc
    co
    #
    caddc
    co
    #
    @0
    cc0
    @8
    cfzo
    co
    #
    cin
    cK
    cfv
    #
    @11
    caddc
    co
    cA
    @24
    cin
    cK
    cfv
    #
    cB
    @24
    cin
    cK
    cfv
    #
    caddc
    co
    wph
    @3
    @6
    @11
    caddc
    co
    #
    caddc
    co
    #
    @14
    @19
    caddc
    co
    #
    @16
    @21
    caddc
    co
    #
    caddc
    co
    #
    @12
    @23
    wph
    @29
    @32
    c0
    cN
    cC
    cfv
    wcel
    #
    @5
    cc0
    cif
    #
    wph
    @3
    @28
    wph
    @3
    wph
    @2
    cn0
    cpw
    cfn
    cin
    #
    wcel
    #
    @3
    cn0
    wcel
    wph
    @2
    cn0
    wss
    @2
    cfn
    wcel
    #
    @36
    wph
    @2
    @0
    cn0
    @0
    @1
    inss1
    wph
    @0
    vk
    cv
    #
    cA
    wcel
    @38
    cB
    wcel
    c0
    @38
    cC
    cfv
    wcel
    whad
    #
    vk
    cn0
    crab
    cn0
    wph
    cA
    cB
    cC
    vk
    vm
    vn
    vc
    sadval.a
    sadval.b
    sadval.c
    sadfval
    @39
    vk
    cn0
    ssrab2
    syl6eqss
    #
    syl5ss
    wph
    @1
    cfn
    wcel
    #
    @2
    @1
    wss
    @37
    @41
    wph
    cc0
    cN
    fzofi
    a1i
    #
    @0
    @1
    inss2
    @1
    @2
    ssfi
    sylancl
    @2
    cn0
    elfpw
    sylanbrc
    @35
    cn0
    @2
    cK
    @35
    cn0
    cK
    wf
    @35
    cn0
    cbits
    cn0
    cres
    #
    ccnv
    #
    wf
    #
    cn0
    @35
    @43
    wf1o
    @35
    cn0
    @44
    wf1o
    @45
    bitsf1o
    cn0
    @35
    @43
    f1ocnv
    @35
    cn0
    @44
    f1of
    mp2b
    @35
    cn0
    cK
    @44
    sadcadd.k
    feq1i
    mpbir
    #
    ffvelrni
    syl
    nn0cnd
    #
    wph
    @6
    @11
    wph
    @6
    wph
    @5
    cn0
    wcel
    #
    cc0
    cn0
    wcel
    #
    @6
    cn0
    wcel
    wph
    c2
    cN
    c2
    cn0
    wcel
    wph
    2nn0
    a1i
    #
    sadcp1.n
    nn0expcld
    #
    0nn0
    @4
    @5
    cc0
    cn0
    ifcl
    sylancl
    nn0cnd
    #
    wph
    @11
    wph
    @10
    cn0
    wcel
    @49
    @11
    cn0
    wcel
    wph
    c2
    @8
    @50
    wph
    cN
    c1
    sadcp1.n
    c1
    cn0
    wcel
    wph
    1nn0
    a1i
    nn0addcld
    nn0expcld
    0nn0
    @9
    @10
    cc0
    cn0
    ifcl
    sylancl
    nn0cnd
    #
    addcld
    #
    addcld
    wph
    @30
    @31
    wph
    @14
    @19
    wph
    @14
    wph
    @13
    @35
    wcel
    #
    @14
    cn0
    wcel
    wph
    @13
    cn0
    wss
    @13
    cfn
    wcel
    #
    @55
    wph
    @13
    cA
    cn0
    cA
    @1
    inss1
    sadval.a
    syl5ss
    wph
    @41
    @13
    @1
    wss
    @56
    @42
    cA
    @1
    inss2
    @1
    @13
    ssfi
    sylancl
    @13
    cn0
    elfpw
    sylanbrc
    @35
    cn0
    @13
    cK
    @46
    ffvelrni
    syl
    nn0cnd
    #
    wph
    @19
    wph
    @18
    @35
    wcel
    #
    @19
    cn0
    wcel
    wph
    @18
    cn0
    wss
    @18
    cfn
    wcel
    #
    @58
    wph
    @18
    cB
    cn0
    cB
    @1
    inss1
    sadval.b
    syl5ss
    wph
    @41
    @18
    @1
    wss
    @59
    @42
    cB
    @1
    inss2
    @1
    @18
    ssfi
    sylancl
    @18
    cn0
    elfpw
    sylanbrc
    @35
    cn0
    @18
    cK
    @46
    ffvelrni
    syl
    nn0cnd
    #
    addcld
    #
    wph
    @16
    @21
    wph
    @16
    wph
    @48
    @49
    @16
    cn0
    wcel
    @51
    0nn0
    @15
    @5
    cc0
    cn0
    ifcl
    sylancl
    nn0cnd
    #
    wph
    @21
    wph
    @48
    @49
    @21
    cn0
    wcel
    @51
    0nn0
    @20
    @5
    cc0
    cn0
    ifcl
    sylancl
    nn0cnd
    #
    addcld
    #
    addcld
    wph
    @33
    @5
    cc0
    cc
    wph
    @5
    cc
    wcel
    #
    @33
    wph
    @5
    @51
    nn0cnd
    #
    adantr
    wph
    @33
    wn
    wa
    0cnd
    ifclda
    #
    wph
    @3
    @34
    caddc
    co
    #
    @28
    caddc
    co
    @30
    @31
    @34
    caddc
    co
    #
    caddc
    co
    @29
    @34
    caddc
    co
    @32
    @34
    caddc
    co
    wph
    @68
    @30
    @28
    @69
    caddc
    sadadd2lem.1
    wph
    @28
    @15
    @20
    @33
    whad
    #
    @5
    cc0
    cif
    #
    @15
    @20
    @33
    wcad
    #
    c2
    @5
    cmul
    co
    #
    cc0
    cif
    #
    caddc
    co
    #
    @69
    wph
    @6
    @71
    @11
    @74
    caddc
    wph
    @4
    @70
    @5
    cc0
    wph
    cA
    cB
    cC
    vm
    vn
    cN
    vc
    sadval.a
    sadval.b
    sadval.c
    sadcp1.n
    sadval
    ifbid
    wph
    @9
    @72
    @10
    @73
    cc0
    wph
    cA
    cB
    cC
    vm
    vn
    cN
    vc
    sadval.a
    sadval.b
    sadval.c
    sadcp1.n
    sadcp1
    wph
    @10
    @5
    c2
    cmul
    co
    @73
    wph
    c2
    cN
    wph
    c2
    @50
    nn0cnd
    #
    sadcp1.n
    expp1d
    wph
    @5
    c2
    @66
    @76
    mulcomd
    eqtrd
    ifbieq1d
    oveq12d
    wph
    @65
    @75
    @69
    wceq
    @66
    @15
    @20
    @33
    @5
    sadadd2lem2
    syl
    eqtrd
    oveq12d
    wph
    @3
    @28
    @34
    @47
    @54
    @67
    add32d
    wph
    @30
    @31
    @34
    @61
    @64
    @67
    addassd
    3eqtr4d
    addcan2ad
    wph
    @3
    @6
    @11
    @47
    @52
    @53
    addassd
    wph
    @14
    @16
    @19
    @21
    @57
    @62
    @60
    @63
    add4d
    3eqtr4d
    wph
    @25
    @7
    @11
    caddc
    wph
    @0
    cn0
    wss
    cN
    cn0
    wcel
    #
    @25
    @7
    wceq
    @40
    sadcp1.n
    @0
    cK
    cN
    sadcadd.k
    bitsinvp1
    syl2anc
    oveq1d
    wph
    @26
    @17
    @27
    @22
    caddc
    wph
    cA
    cn0
    wss
    @77
    @26
    @17
    wceq
    sadval.a
    sadcp1.n
    cA
    cK
    cN
    sadcadd.k
    bitsinvp1
    syl2anc
    wph
    cB
    cn0
    wss
    @77
    @27
    @22
    wceq
    sadval.b
    sadcp1.n
    cB
    cK
    cN
    sadcadd.k
    bitsinvp1
    syl2anc
    oveq12d
    3eqtr4d
end
