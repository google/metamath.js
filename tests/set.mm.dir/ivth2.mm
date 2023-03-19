include "cv.mm"
include "cfv.mm"
include "cneg.mm"
include "cmpt.mm"
include "wceq.mm"
include "cioo.mm"
include "co.mm"
include "wrex.mm"
include "renegcld.mm"
include "cc.mm"
include "ccncf.mm"
include "wcel.mm"
include "eqid.mm"
include "negfcncf.mm"
include "syl.mm"
include "cicc.mm"
include "wa.mm"
include "cr.mm"
include "sselda.mm"
include "fveq2.mm"
include "negeqd.mm"
include "negex.mm"
include "fvmpt.mm"
include "eqeltrd.mm"
include "clt.mm"
include "wbr.mm"
include "cxr.mm"
include "cle.mm"
include "rexrd.mm"
include "ltled.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "simprd.mm"
include "wral.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "ltnegd.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "simpld.mm"
include "ubicc2.mm"
include "breqtrrd.mm"
include "jca.mm"
include "ivth.mm"
include "ioossicc.mm"
include "syl5ss.mm"
include "eqeq1d.mm"
include "wf.mm"
include "cncff.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "recnd.mm"
include "adantr.mm"
include "neg11ad.mm"
include "bitrd.mm"
include "rexbidva.mm"

theorem ivth2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cU: class U
  let cF: class F
  let vc: setvar c
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cS: class S
  assume ivth.1: |- ( ph -> A e. RR )
  assume ivth.2: |- ( ph -> B e. RR )
  assume ivth.3: |- ( ph -> U e. RR )
  assume ivth.4: |- ( ph -> A < B )
  assume ivth.5: |- ( ph -> ( A [,] B ) C_ D )
  assume ivth.7: |- ( ph -> F e. ( D -cn-> CC ) )
  assume ivth.8: |- ( ( ph /\ x e. ( A [,] B ) ) -> ( F ` x ) e. RR )
  assume ivth2.9: |- ( ph -> ( ( F ` B ) < U /\ U < ( F ` A ) ) )

  disjoint c x
  disjoint B c
  disjoint B x
  disjoint D c
  disjoint D x
  disjoint F c
  disjoint F x
  disjoint c ph
  disjoint ph x
  disjoint A c
  disjoint A x
  disjoint U c
  disjoint U x
  disjoint c y
  disjoint c z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint D y
  disjoint D z
  disjoint F y
  disjoint F z
  disjoint ph y
  disjoint ph z
  disjoint A y
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint U y
  disjoint U z
  assert |- ( ph -> E. c e. ( A (,) B ) ( F ` c ) = U )

  proof
    wph
    vc
    cv
    #
    vy
    cD
    vy
    cv
    #
    cF
    cfv
    #
    cneg
    #
    cmpt
    #
    cfv
    #
    cU
    cneg
    #
    wceq
    #
    vc
    cA
    cB
    cioo
    co
    #
    wrex
    @0
    cF
    cfv
    #
    cU
    wceq
    #
    vc
    @8
    wrex
    wph
    vx
    cA
    cB
    cD
    @6
    @4
    vc
    ivth.1
    ivth.2
    wph
    cU
    ivth.3
    renegcld
    ivth.4
    ivth.5
    wph
    cF
    cD
    cc
    ccncf
    co
    #
    wcel
    #
    @4
    @11
    wcel
    ivth.7
    vy
    cD
    cF
    @4
    @4
    eqid
    #
    negfcncf
    syl
    wph
    vx
    cv
    #
    cA
    cB
    cicc
    co
    #
    wcel
    wa
    #
    @14
    @4
    cfv
    #
    @14
    cF
    cfv
    #
    cneg
    #
    cr
    @16
    @14
    cD
    wcel
    @17
    @19
    wceq
    wph
    @15
    cD
    @14
    ivth.5
    sselda
    vy
    @14
    @3
    @19
    cD
    @4
    @1
    @14
    wceq
    @2
    @18
    @1
    @14
    cF
    fveq2
    negeqd
    @13
    @18
    negex
    fvmpt
    syl
    @16
    @18
    ivth.8
    renegcld
    eqeltrd
    wph
    cA
    @4
    cfv
    #
    @6
    clt
    wbr
    @6
    cB
    @4
    cfv
    #
    clt
    wbr
    wph
    @20
    cA
    cF
    cfv
    #
    cneg
    #
    @6
    clt
    wph
    cA
    cD
    wcel
    @20
    @23
    wceq
    wph
    @15
    cD
    cA
    ivth.5
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    cA
    @15
    wcel
    #
    wph
    cA
    ivth.1
    rexrd
    #
    wph
    cB
    ivth.2
    rexrd
    #
    wph
    cA
    cB
    ivth.1
    ivth.2
    ivth.4
    ltled
    #
    cA
    cB
    lbicc2
    syl3anc
    #
    sseldd
    vy
    cA
    @3
    @23
    cD
    @4
    @1
    cA
    wceq
    @2
    @22
    @1
    cA
    cF
    fveq2
    negeqd
    @13
    @22
    negex
    fvmpt
    syl
    wph
    cU
    @22
    clt
    wbr
    #
    @23
    @6
    clt
    wbr
    wph
    cB
    cF
    cfv
    #
    cU
    clt
    wbr
    #
    @32
    ivth2.9
    simprd
    wph
    cU
    @22
    ivth.3
    wph
    @27
    @18
    cr
    wcel
    #
    vx
    @15
    wral
    #
    @22
    cr
    wcel
    #
    @31
    wph
    @35
    vx
    @15
    ivth.8
    ralrimiva
    #
    @35
    @37
    vx
    cA
    @15
    @14
    cA
    wceq
    @18
    @22
    cr
    @14
    cA
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    ltnegd
    mpbid
    eqbrtrd
    wph
    @6
    @33
    cneg
    #
    @21
    clt
    wph
    @34
    @6
    @39
    clt
    wbr
    wph
    @34
    @32
    ivth2.9
    simpld
    wph
    @33
    cU
    wph
    cB
    @15
    wcel
    #
    @36
    @33
    cr
    wcel
    #
    wph
    @24
    @25
    @26
    @40
    @28
    @29
    @30
    cA
    cB
    ubicc2
    syl3anc
    #
    @38
    @35
    @41
    vx
    cB
    @15
    @14
    cB
    wceq
    @18
    @33
    cr
    @14
    cB
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    ivth.3
    ltnegd
    mpbid
    wph
    cB
    cD
    wcel
    @21
    @39
    wceq
    wph
    @15
    cD
    cB
    ivth.5
    @42
    sseldd
    vy
    cB
    @3
    @39
    cD
    @4
    @1
    cB
    wceq
    @2
    @33
    @1
    cB
    cF
    fveq2
    negeqd
    @13
    @33
    negex
    fvmpt
    syl
    breqtrrd
    jca
    ivth
    wph
    @7
    @10
    vc
    @8
    wph
    @0
    @8
    wcel
    #
    wa
    #
    @7
    @9
    cneg
    #
    @6
    wceq
    @10
    @44
    @5
    @45
    @6
    @44
    @0
    cD
    wcel
    #
    @5
    @45
    wceq
    wph
    @8
    cD
    @0
    wph
    @8
    @15
    cD
    cA
    cB
    ioossicc
    ivth.5
    syl5ss
    sselda
    #
    vy
    @0
    @3
    @45
    cD
    @4
    @1
    @0
    wceq
    @2
    @9
    @1
    @0
    cF
    fveq2
    negeqd
    @13
    @9
    negex
    fvmpt
    syl
    eqeq1d
    @44
    @9
    cU
    wph
    @43
    @46
    @9
    cc
    wcel
    @47
    wph
    cD
    cc
    @0
    cF
    wph
    @12
    cD
    cc
    cF
    wf
    ivth.7
    cD
    cc
    cF
    cncff
    syl
    ffvelrnda
    syldan
    wph
    cU
    cc
    wcel
    @43
    wph
    cU
    ivth.3
    recnd
    adantr
    neg11ad
    bitrd
    rexbidva
    mpbid
end
