include "cexp.mm"
include "co.mm"
include "cli.mm"
include "wbr.mm"
include "cc.mm"
include "cv.mm"
include "cmpt.mm"
include "ccom.mm"
include "cfv.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "ccn.mm"
include "ccncf.mm"
include "cn0.mm"
include "wcel.mm"
include "eqid.mm"
include "expcn.mm"
include "syl.mm"
include "cncfcn1.mm"
include "syl6eleqr.mm"
include "climcl.mm"
include "climcncf.mm"
include "eqidd.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "oveq1d.mm"
include "expcld.mm"
include "fvmptd.mm"
include "breqtrd.mm"
include "cvv.mm"
include "cnex.mm"
include "mptex.mm"
include "wf.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fex.mm"
include "sylancl.mm"
include "coexg.mm"
include "sylancr.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "fvco3.mm"
include "sylan.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfov.mm"
include "nfeq.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "3eqtr4rd.mm"
include "climeq.mm"
include "mpbird.mm"

theorem climexp
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cH: class H
  let cM: class M
  let cN: class N
  let cV: class V
  let cZ: class Z
  let vj: setvar j
  let vx: setvar x
  assume climexp.1: |- F/ k ph
  assume climexp.2: |- F/_ k F
  assume climexp.3: |- F/_ k H
  assume climexp.4: |- Z = ( ZZ>= ` M )
  assume climexp.5: |- ( ph -> M e. ZZ )
  assume climexp.6: |- ( ph -> F : Z --> CC )
  assume climexp.7: |- ( ph -> F ~~> A )
  assume climexp.8: |- ( ph -> N e. NN0 )
  assume climexp.9: |- ( ph -> H e. V )
  assume climexp.10: |- ( ( ph /\ k e. Z ) -> ( H ` k ) = ( ( F ` k ) ^ N ) )

  disjoint N k
  disjoint Z k
  disjoint j k
  disjoint j x
  disjoint j ph
  disjoint ph x
  disjoint A j
  disjoint A x
  disjoint F j
  disjoint F x
  disjoint H j
  disjoint N j
  disjoint N x
  disjoint Z j
  disjoint Z x
  assert |- ( ph -> H ~~> ( A ^ N ) )

  proof
    wph
    cH
    cA
    cN
    cexp
    co
    #
    cli
    wbr
    vx
    cc
    vx
    cv
    #
    cN
    cexp
    co
    #
    cmpt
    #
    cF
    ccom
    #
    @0
    cli
    wbr
    wph
    @4
    cA
    @3
    cfv
    @0
    cli
    wph
    cc
    cc
    cA
    @3
    cF
    cM
    cZ
    climexp.4
    climexp.5
    wph
    @3
    ccnfld
    ctopn
    cfv
    #
    @5
    ccn
    co
    #
    cc
    cc
    ccncf
    co
    wph
    cN
    cn0
    wcel
    #
    @3
    @6
    wcel
    climexp.8
    vx
    @5
    cN
    @5
    eqid
    #
    expcn
    syl
    @5
    @8
    cncfcn1
    syl6eleqr
    climexp.6
    climexp.7
    wph
    cF
    cA
    cli
    wbr
    cA
    cc
    wcel
    climexp.7
    cA
    cF
    climcl
    syl
    #
    climcncf
    wph
    vx
    cA
    @2
    @0
    cc
    @3
    cc
    wph
    @3
    eqidd
    wph
    @1
    cA
    wceq
    #
    wa
    @1
    cA
    cN
    cexp
    wph
    @10
    simpr
    oveq1d
    @9
    wph
    cA
    cN
    @9
    climexp.8
    expcld
    fvmptd
    breqtrd
    wph
    @0
    vj
    cH
    @4
    cM
    cV
    cvv
    cZ
    climexp.4
    climexp.9
    wph
    @3
    cvv
    wcel
    cF
    cvv
    wcel
    #
    @4
    cvv
    wcel
    vx
    cc
    @2
    cnex
    mptex
    wph
    cZ
    cc
    cF
    wf
    #
    cZ
    cvv
    wcel
    @11
    climexp.6
    cZ
    cM
    cuz
    cfv
    cvv
    climexp.4
    cM
    cuz
    fvex
    eqeltri
    cZ
    cc
    cvv
    cF
    fex
    sylancl
    @3
    cF
    cvv
    cvv
    coexg
    sylancr
    climexp.5
    wph
    vj
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @13
    cF
    cfv
    #
    @3
    cfv
    #
    @16
    cN
    cexp
    co
    #
    @13
    @4
    cfv
    #
    @13
    cH
    cfv
    #
    @15
    vx
    @16
    @2
    @18
    cc
    @3
    cc
    @15
    @3
    eqidd
    @15
    @1
    @16
    wceq
    #
    wa
    @1
    @16
    cN
    cexp
    @15
    @21
    simpr
    oveq1d
    wph
    cZ
    cc
    @13
    cF
    climexp.6
    ffvelrnda
    #
    @15
    @16
    cN
    @22
    wph
    @7
    @14
    climexp.8
    adantr
    expcld
    fvmptd
    wph
    @12
    @14
    @19
    @17
    wceq
    climexp.6
    cZ
    cc
    @13
    @3
    cF
    fvco3
    sylan
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @23
    cH
    cfv
    #
    @23
    cF
    cfv
    #
    cN
    cexp
    co
    #
    wceq
    #
    wi
    @15
    @20
    @18
    wceq
    #
    wi
    vk
    vj
    @15
    @30
    vk
    wph
    @14
    vk
    climexp.1
    @14
    vk
    nfv
    nfan
    vk
    @20
    @18
    vk
    @13
    cH
    climexp.3
    vk
    @13
    nfcv
    #
    nffv
    vk
    @16
    cN
    cexp
    vk
    @13
    cF
    climexp.2
    @31
    nffv
    vk
    cexp
    nfcv
    vk
    cN
    nfcv
    nfov
    nfeq
    nfim
    @23
    @13
    wceq
    #
    @25
    @15
    @29
    @30
    @32
    @24
    @14
    wph
    @23
    @13
    cZ
    eleq1
    anbi2d
    @32
    @26
    @20
    @28
    @18
    @23
    @13
    cH
    fveq2
    @32
    @27
    @16
    cN
    cexp
    @23
    @13
    cF
    fveq2
    oveq1d
    eqeq12d
    imbi12d
    climexp.10
    chvar
    3eqtr4rd
    climeq
    mpbird
end
