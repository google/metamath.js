include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "caddc.mm"
include "co.mm"
include "cfallfac.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "cmin.mm"
include "cmul.mm"
include "csu.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "csn.mm"
include "c1.mm"
include "oveq2.mm"
include "cz.mm"
include "0z.mm"
include "fzsn.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "adantr.mm"
include "sumeq12dv.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "fallfac0.mm"
include "oveqan12d.mm"
include "1t1e1.mm"
include "0cn.mm"
include "ax-1cn.mm"
include "syl6eqel.mm"
include "0nn0.mm"
include "bcnn.mm"
include "0m0e0.mm"
include "sumsn.mm"
include "sylancr.mm"
include "addcl.mm"
include "syl.mm"
include "3eqtr4rd.mm"
include "simprl.mm"
include "simprr.mm"
include "simpl.mm"
include "id.mm"
include "binomfallfaclem2.mm"
include "exp31.mm"
include "a2d.mm"
include "nn0ind.mm"
include "com12.mm"
include "3impia.mm"

theorem binomfallfac
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cN: class N
  let vm: setvar m
  let vn: setvar n

  disjoint A k
  disjoint B k
  disjoint N k
  disjoint A m
  disjoint A n
  disjoint B m
  disjoint B n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint N m
  assert |- ( ( A e. CC /\ B e. CC /\ N e. NN0 ) -> ( ( A + B ) FallFac N ) = sum_ k e. ( 0 ... N ) ( ( N _C k ) x. ( ( A FallFac ( N - k ) ) x. ( B FallFac k ) ) ) )

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
    caddc
    co
    #
    cN
    cfallfac
    co
    #
    cc0
    cN
    cfz
    co
    #
    cN
    vk
    cv
    #
    cbc
    co
    #
    cA
    cN
    @6
    cmin
    co
    #
    cfallfac
    co
    #
    cB
    @6
    cfallfac
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    wceq
    #
    @2
    @0
    @1
    wa
    #
    @14
    @15
    @3
    vm
    cv
    #
    cfallfac
    co
    #
    cc0
    @16
    cfz
    co
    #
    @16
    @6
    cbc
    co
    #
    cA
    @16
    @6
    cmin
    co
    #
    cfallfac
    co
    #
    @10
    cmul
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    wceq
    #
    wi
    @15
    @3
    cc0
    cfallfac
    co
    #
    cc0
    csn
    #
    cc0
    @6
    cbc
    co
    #
    cA
    cc0
    @6
    cmin
    co
    #
    cfallfac
    co
    #
    @10
    cmul
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    wceq
    #
    wi
    @15
    @3
    vn
    cv
    #
    cfallfac
    co
    #
    cc0
    @35
    cfz
    co
    #
    @35
    @6
    cbc
    co
    #
    cA
    @35
    @6
    cmin
    co
    #
    cfallfac
    co
    #
    @10
    cmul
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    wceq
    #
    wi
    @15
    @3
    @35
    c1
    caddc
    co
    #
    cfallfac
    co
    #
    cc0
    @45
    cfz
    co
    #
    @45
    @6
    cbc
    co
    #
    cA
    @45
    @6
    cmin
    co
    #
    cfallfac
    co
    #
    @10
    cmul
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    wceq
    #
    wi
    @15
    @14
    wi
    vm
    vn
    cN
    @16
    cc0
    wceq
    #
    @25
    @34
    @15
    @55
    @17
    @26
    @24
    @33
    @16
    cc0
    @3
    cfallfac
    oveq2
    @55
    @18
    @27
    @23
    @32
    vk
    @55
    @18
    cc0
    cc0
    cfz
    co
    #
    @27
    @16
    cc0
    cc0
    cfz
    oveq2
    cc0
    cz
    wcel
    @56
    @27
    wceq
    0z
    cc0
    fzsn
    ax-mp
    syl6eq
    @55
    @23
    @32
    wceq
    @6
    @18
    wcel
    #
    @55
    @19
    @28
    @22
    @31
    cmul
    @16
    cc0
    @6
    cbc
    oveq1
    @55
    @21
    @30
    @10
    cmul
    @55
    @20
    @29
    cA
    cfallfac
    @16
    cc0
    @6
    cmin
    oveq1
    oveq2d
    oveq1d
    oveq12d
    adantr
    sumeq12dv
    eqeq12d
    imbi2d
    vm
    vn
    weq
    #
    @25
    @44
    @15
    @58
    @17
    @36
    @24
    @43
    @16
    @35
    @3
    cfallfac
    oveq2
    @58
    @18
    @37
    @23
    @42
    vk
    @16
    @35
    cc0
    cfz
    oveq2
    @58
    @23
    @42
    wceq
    @57
    @58
    @19
    @38
    @22
    @41
    cmul
    @16
    @35
    @6
    cbc
    oveq1
    @58
    @21
    @40
    @10
    cmul
    @58
    @20
    @39
    cA
    cfallfac
    @16
    @35
    @6
    cmin
    oveq1
    oveq2d
    oveq1d
    oveq12d
    adantr
    sumeq12dv
    eqeq12d
    imbi2d
    @16
    @45
    wceq
    #
    @25
    @54
    @15
    @59
    @17
    @46
    @24
    @53
    @16
    @45
    @3
    cfallfac
    oveq2
    @59
    @18
    @47
    @23
    @52
    vk
    @16
    @45
    cc0
    cfz
    oveq2
    @59
    @23
    @52
    wceq
    @57
    @59
    @19
    @48
    @22
    @51
    cmul
    @16
    @45
    @6
    cbc
    oveq1
    @59
    @21
    @50
    @10
    cmul
    @59
    @20
    @49
    cA
    cfallfac
    @16
    @45
    @6
    cmin
    oveq1
    oveq2d
    oveq1d
    oveq12d
    adantr
    sumeq12dv
    eqeq12d
    imbi2d
    @16
    cN
    wceq
    #
    @25
    @14
    @15
    @60
    @17
    @4
    @24
    @13
    @16
    cN
    @3
    cfallfac
    oveq2
    @60
    @18
    @5
    @23
    @12
    vk
    @16
    cN
    cc0
    cfz
    oveq2
    @60
    @23
    @12
    wceq
    @57
    @60
    @19
    @7
    @22
    @11
    cmul
    @16
    cN
    @6
    cbc
    oveq1
    @60
    @21
    @9
    @10
    cmul
    @60
    @20
    @8
    cA
    cfallfac
    @16
    cN
    @6
    cmin
    oveq1
    oveq2d
    oveq1d
    oveq12d
    adantr
    sumeq12dv
    eqeq12d
    imbi2d
    @15
    c1
    cA
    cc0
    cfallfac
    co
    #
    cB
    cc0
    cfallfac
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    c1
    @33
    @26
    @15
    @64
    c1
    c1
    cmul
    co
    #
    c1
    @15
    @63
    c1
    c1
    cmul
    @15
    @63
    @65
    c1
    @0
    @1
    @61
    c1
    @62
    c1
    cmul
    cA
    fallfac0
    cB
    fallfac0
    oveqan12d
    1t1e1
    syl6eq
    oveq2d
    1t1e1
    syl6eq
    #
    @15
    cc0
    cc
    wcel
    @64
    cc
    wcel
    @33
    @64
    wceq
    0cn
    @15
    @64
    c1
    cc
    @66
    ax-1cn
    syl6eqel
    @32
    @64
    vk
    cc0
    cc
    @6
    cc0
    wceq
    #
    @28
    c1
    @31
    @63
    cmul
    @67
    @28
    cc0
    cc0
    cbc
    co
    #
    c1
    @6
    cc0
    cc0
    cbc
    oveq2
    cc0
    cn0
    wcel
    @68
    c1
    wceq
    0nn0
    cc0
    bcnn
    ax-mp
    syl6eq
    @67
    @30
    @61
    @10
    @62
    cmul
    @67
    @29
    cc0
    cA
    cfallfac
    @67
    @29
    cc0
    cc0
    cmin
    co
    cc0
    @6
    cc0
    cc0
    cmin
    oveq2
    0m0e0
    syl6eq
    oveq2d
    @6
    cc0
    cB
    cfallfac
    oveq2
    oveq12d
    oveq12d
    sumsn
    sylancr
    @15
    @3
    cc
    wcel
    @26
    c1
    wceq
    cA
    cB
    addcl
    @3
    fallfac0
    syl
    3eqtr4rd
    @35
    cn0
    wcel
    #
    @15
    @44
    @54
    @69
    @15
    @44
    @54
    @69
    @15
    wa
    @44
    cA
    cB
    vk
    @35
    @69
    @0
    @1
    simprl
    @69
    @0
    @1
    simprr
    @69
    @15
    simpl
    @44
    id
    binomfallfaclem2
    exp31
    a2d
    nn0ind
    com12
    3impia
end
