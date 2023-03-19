include "csad.mm"
include "co.mm"
include "wcel.mm"
include "c0.mm"
include "cfv.mm"
include "whad.mm"
include "wxo.mm"
include "cun.mm"
include "sadval.mm"
include "wn.mm"
include "wb.mm"
include "cn0.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "notbid.mm"
include "imbi2d.mm"
include "sadc0.mm"
include "wa.mm"
include "noel.mm"
include "wcad.mm"
include "wss.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "sadcp1.mm"
include "cad0.mm"
include "adantl.mm"
include "cin.mm"
include "elin.mm"
include "syl5bbr.mm"
include "3bitrd.mm"
include "mtbiri.mm"
include "ex.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "mpcom.mm"
include "hadrot.mm"
include "had0.mm"
include "syl.mm"
include "wo.mm"
include "xor2.mm"
include "rbaib.mm"
include "elun.mm"
include "syl6bbr.mm"

theorem saddisjlem
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
  assume saddisj.1: |- ( ph -> A C_ NN0 )
  assume saddisj.2: |- ( ph -> B C_ NN0 )
  assume saddisj.3: |- ( ph -> ( A i^i B ) = (/) )
  assume saddisjlem.c: |- C = seq 0 ( ( c e. 2o , m e. NN0 |-> if ( cadd ( m e. A , m e. B , (/) e. c ) , 1o , (/) ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )
  assume saddisjlem.3: |- ( ph -> N e. NN0 )

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
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m x
  disjoint n x
  disjoint A k
  disjoint B k
  disjoint C k
  disjoint C x
  disjoint k ph
  disjoint ph x
  disjoint N x
  assert |- ( ph -> ( N e. ( A sadd B ) <-> N e. ( A u. B ) ) )

  proof
    wph
    cN
    cA
    cB
    csad
    co
    wcel
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
    whad
    #
    @0
    @1
    wxo
    #
    cN
    cA
    cB
    cun
    wcel
    #
    wph
    cA
    cB
    cC
    vm
    vn
    cN
    vc
    saddisj.1
    saddisj.2
    saddisjlem.c
    saddisjlem.3
    sadval
    wph
    @3
    wn
    #
    @4
    @5
    wb
    cN
    cn0
    wcel
    wph
    @7
    saddisjlem.3
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
    wn
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
    wn
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
    wn
    #
    wi
    wph
    c0
    @15
    c1
    caddc
    co
    #
    cC
    cfv
    #
    wcel
    #
    wn
    #
    wi
    wph
    @7
    wi
    vx
    vk
    cN
    @8
    cc0
    wceq
    #
    @11
    @14
    wph
    @23
    @10
    @13
    @23
    @9
    @12
    c0
    @8
    cc0
    cC
    fveq2
    eleq2d
    notbid
    imbi2d
    @8
    @15
    wceq
    #
    @11
    @18
    wph
    @24
    @10
    @17
    @24
    @9
    @16
    c0
    @8
    @15
    cC
    fveq2
    eleq2d
    notbid
    imbi2d
    @8
    @19
    wceq
    #
    @11
    @22
    wph
    @25
    @10
    @21
    @25
    @9
    @20
    c0
    @8
    @19
    cC
    fveq2
    eleq2d
    notbid
    imbi2d
    @8
    cN
    wceq
    #
    @11
    @7
    wph
    @26
    @10
    @3
    @26
    @9
    @2
    c0
    @8
    cN
    cC
    fveq2
    eleq2d
    notbid
    imbi2d
    wph
    cA
    cB
    cC
    vm
    vn
    vc
    saddisj.1
    saddisj.2
    saddisjlem.c
    sadc0
    @15
    cn0
    wcel
    #
    wph
    @18
    @22
    wph
    @27
    @18
    @22
    wi
    wph
    @27
    wa
    #
    @18
    @22
    @28
    @18
    wa
    #
    @21
    @15
    c0
    wcel
    #
    @15
    noel
    @29
    @21
    @15
    cA
    wcel
    #
    @15
    cB
    wcel
    #
    @17
    wcad
    #
    @31
    @32
    wa
    #
    @30
    @29
    cA
    cB
    cC
    vm
    vn
    @15
    vc
    wph
    cA
    cn0
    wss
    @27
    @18
    saddisj.1
    ad2antrr
    wph
    cB
    cn0
    wss
    @27
    @18
    saddisj.2
    ad2antrr
    saddisjlem.c
    wph
    @27
    @18
    simplr
    sadcp1
    @18
    @33
    @34
    wb
    @28
    @31
    @32
    @17
    cad0
    adantl
    @34
    @15
    cA
    cB
    cin
    #
    wcel
    @29
    @30
    @15
    cA
    cB
    elin
    @29
    @35
    c0
    @15
    wph
    @35
    c0
    wceq
    @27
    @18
    saddisj.3
    ad2antrr
    eleq2d
    syl5bbr
    3bitrd
    mtbiri
    ex
    expcom
    a2d
    nn0ind
    mpcom
    @4
    @3
    @0
    @1
    whad
    @7
    @5
    @3
    @0
    @1
    hadrot
    @3
    @0
    @1
    had0
    syl5bbr
    syl
    wph
    @5
    @0
    @1
    wo
    #
    @6
    wph
    @0
    @1
    wa
    #
    wn
    #
    @5
    @36
    wb
    wph
    @37
    cN
    c0
    wcel
    #
    cN
    noel
    @37
    cN
    @35
    wcel
    wph
    @39
    cN
    cA
    cB
    elin
    wph
    @35
    c0
    cN
    saddisj.3
    eleq2d
    syl5bbr
    mtbiri
    @5
    @36
    @38
    @0
    @1
    xor2
    rbaib
    syl
    cN
    cA
    cB
    elun
    syl6bbr
    3bitrd
end
