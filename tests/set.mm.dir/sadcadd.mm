include "cn0.mm"
include "wcel.mm"
include "c0.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "cin.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "oveq2.mm"
include "cc.mm"
include "2cn.mm"
include "exp0.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "fzo0.mm"
include "ineq2d.mm"
include "in0.mm"
include "fveq2d.mm"
include "cbits.mm"
include "cres.mm"
include "ccnv.mm"
include "0nn0.mm"
include "fvres.mm"
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
include "oveq12d.mm"
include "00id.mm"
include "breq12d.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "sadc0.mm"
include "wn.mm"
include "clt.mm"
include "0lt1.mm"
include "0re.mm"
include "1re.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "a1i.mm"
include "2falsed.mm"
include "wa.mm"
include "wss.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "sadcaddlem.mm"
include "ex.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "mpcom.mm"

theorem sadcadd
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
  assert |- ( ph -> ( (/) e. ( C ` N ) <-> ( 2 ^ N ) <_ ( ( K ` ( A i^i ( 0 ..^ N ) ) ) + ( K ` ( B i^i ( 0 ..^ N ) ) ) ) ) )

  proof
    cN
    cn0
    wcel
    wph
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
    cA
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
    cB
    @3
    cin
    #
    cK
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    #
    wb
    #
    sadcp1.n
    wph
    c0
    vx
    cv
    #
    cC
    cfv
    #
    wcel
    #
    c2
    @11
    cexp
    co
    #
    cA
    cc0
    @11
    cfzo
    co
    #
    cin
    #
    cK
    cfv
    #
    cB
    @15
    cin
    #
    cK
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    #
    wb
    #
    wi
    wph
    c0
    cc0
    cC
    cfv
    #
    wcel
    #
    c1
    cc0
    cle
    wbr
    #
    wb
    #
    wi
    wph
    c0
    vk
    cv
    #
    cC
    cfv
    #
    wcel
    #
    c2
    @27
    cexp
    co
    #
    cA
    cc0
    @27
    cfzo
    co
    #
    cin
    #
    cK
    cfv
    #
    cB
    @31
    cin
    #
    cK
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    #
    wb
    #
    wi
    wph
    c0
    @27
    c1
    caddc
    co
    #
    cC
    cfv
    #
    wcel
    #
    c2
    @39
    cexp
    co
    #
    cA
    cc0
    @39
    cfzo
    co
    #
    cin
    #
    cK
    cfv
    #
    cB
    @43
    cin
    #
    cK
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    #
    wb
    #
    wi
    wph
    @10
    wi
    vx
    vk
    cN
    @11
    cc0
    wceq
    #
    @22
    @26
    wph
    @51
    @13
    @24
    @21
    @25
    @51
    @12
    @23
    c0
    @11
    cc0
    cC
    fveq2
    eleq2d
    @51
    @14
    c1
    @20
    cc0
    cle
    @51
    @14
    c2
    cc0
    cexp
    co
    #
    c1
    @11
    cc0
    c2
    cexp
    oveq2
    c2
    cc
    wcel
    @52
    c1
    wceq
    2cn
    c2
    exp0
    ax-mp
    syl6eq
    @51
    @20
    cc0
    cc0
    caddc
    co
    cc0
    @51
    @17
    cc0
    @19
    cc0
    caddc
    @51
    @17
    c0
    cK
    cfv
    #
    cc0
    @51
    @16
    c0
    cK
    @51
    @16
    cA
    c0
    cin
    c0
    @51
    @15
    c0
    cA
    @51
    @15
    cc0
    cc0
    cfzo
    co
    c0
    @11
    cc0
    cc0
    cfzo
    oveq2
    cc0
    fzo0
    syl6eq
    #
    ineq2d
    cA
    in0
    syl6eq
    fveq2d
    @53
    cc0
    cbits
    cn0
    cres
    #
    cfv
    #
    @55
    ccnv
    #
    cfv
    #
    cc0
    c0
    @56
    cK
    @57
    sadcadd.k
    @56
    cc0
    cbits
    cfv
    #
    c0
    cc0
    cn0
    wcel
    #
    @56
    @59
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
    @55
    wf1o
    @60
    @58
    cc0
    wceq
    bitsf1o
    0nn0
    cn0
    @61
    cc0
    @55
    f1ocnvfv1
    mp2an
    eqtri
    #
    syl6eq
    @51
    @19
    @53
    cc0
    @51
    @18
    c0
    cK
    @51
    @18
    cB
    c0
    cin
    c0
    @51
    @15
    c0
    cB
    @54
    ineq2d
    cB
    in0
    syl6eq
    fveq2d
    @62
    syl6eq
    oveq12d
    00id
    syl6eq
    breq12d
    bibi12d
    imbi2d
    @11
    @27
    wceq
    #
    @22
    @38
    wph
    @63
    @13
    @29
    @21
    @37
    @63
    @12
    @28
    c0
    @11
    @27
    cC
    fveq2
    eleq2d
    @63
    @14
    @30
    @20
    @36
    cle
    @11
    @27
    c2
    cexp
    oveq2
    @63
    @17
    @33
    @19
    @35
    caddc
    @63
    @16
    @32
    cK
    @63
    @15
    @31
    cA
    @11
    @27
    cc0
    cfzo
    oveq2
    #
    ineq2d
    fveq2d
    @63
    @18
    @34
    cK
    @63
    @15
    @31
    cB
    @64
    ineq2d
    fveq2d
    oveq12d
    breq12d
    bibi12d
    imbi2d
    @11
    @39
    wceq
    #
    @22
    @50
    wph
    @65
    @13
    @41
    @21
    @49
    @65
    @12
    @40
    c0
    @11
    @39
    cC
    fveq2
    eleq2d
    @65
    @14
    @42
    @20
    @48
    cle
    @11
    @39
    c2
    cexp
    oveq2
    @65
    @17
    @45
    @19
    @47
    caddc
    @65
    @16
    @44
    cK
    @65
    @15
    @43
    cA
    @11
    @39
    cc0
    cfzo
    oveq2
    #
    ineq2d
    fveq2d
    @65
    @18
    @46
    cK
    @65
    @15
    @43
    cB
    @66
    ineq2d
    fveq2d
    oveq12d
    breq12d
    bibi12d
    imbi2d
    @11
    cN
    wceq
    #
    @22
    @10
    wph
    @67
    @13
    @1
    @21
    @9
    @67
    @12
    @0
    c0
    @11
    cN
    cC
    fveq2
    eleq2d
    @67
    @14
    @2
    @20
    @8
    cle
    @11
    cN
    c2
    cexp
    oveq2
    @67
    @17
    @5
    @19
    @7
    caddc
    @67
    @16
    @4
    cK
    @67
    @15
    @3
    cA
    @11
    cN
    cc0
    cfzo
    oveq2
    #
    ineq2d
    fveq2d
    @67
    @18
    @6
    cK
    @67
    @15
    @3
    cB
    @68
    ineq2d
    fveq2d
    oveq12d
    breq12d
    bibi12d
    imbi2d
    wph
    @24
    @25
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
    @25
    wn
    #
    wph
    cc0
    c1
    clt
    wbr
    @69
    0lt1
    cc0
    c1
    0re
    1re
    ltnlei
    mpbi
    a1i
    2falsed
    @27
    cn0
    wcel
    #
    wph
    @38
    @50
    wph
    @70
    @38
    @50
    wi
    wph
    @70
    wa
    #
    @38
    @50
    @71
    @38
    wa
    cA
    cB
    cC
    vm
    vn
    cK
    @27
    vc
    wph
    cA
    cn0
    wss
    @70
    @38
    sadval.a
    ad2antrr
    wph
    cB
    cn0
    wss
    @70
    @38
    sadval.b
    ad2antrr
    sadval.c
    wph
    @70
    @38
    simplr
    sadcadd.k
    @71
    @38
    simpr
    sadcaddlem
    ex
    expcom
    a2d
    nn0ind
    mpcom
end
