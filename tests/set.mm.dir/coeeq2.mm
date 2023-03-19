include "cn0.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "simpll.mm"
include "simpr.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "wb.mm"
include "simplr.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "nn0zd.mm"
include "ad2antrr.mm"
include "elfz5.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "wn.mm"
include "0cnd.mm"
include "ifclda.mm"
include "eqid.mm"
include "fmptd.mm"
include "c1.mm"
include "caddc.mm"
include "cima.mm"
include "csn.mm"
include "wceq.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "fvmpt2.mm"
include "neeq1d.mm"
include "iffalse.mm"
include "necon1ai.mm"
include "syl6bi.mm"
include "ralrimiva.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nfne.mm"
include "nfim.mm"
include "fveq2.mm"
include "breq1.mm"
include "imbi12d.mm"
include "cbvral.mm"
include "sylib.mm"
include "wf.mm"
include "plyco0.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "nfov.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "cbvsumi.mm"
include "elfznn0.mm"
include "adantl.mm"
include "elfzle2.mm"
include "iftrued.mm"
include "adantlr.mm"
include "eqeltrd.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "sumeq2dv.mm"
include "syl5eqr.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "coeeq.mm"

theorem coeeq2
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cN: class N
  let vm: setvar m
  assume dgrle.1: |- ( ph -> F e. ( Poly ` S ) )
  assume dgrle.2: |- ( ph -> N e. NN0 )
  assume dgrle.3: |- ( ( ph /\ k e. ( 0 ... N ) ) -> A e. CC )
  assume dgrle.4: |- ( ph -> F = ( z e. CC |-> sum_ k e. ( 0 ... N ) ( A x. ( z ^ k ) ) ) )

  disjoint A z
  disjoint k z
  disjoint N k
  disjoint N z
  disjoint k ph
  disjoint ph z
  disjoint m z
  disjoint A m
  disjoint F m
  disjoint k m
  disjoint N m
  disjoint m ph
  assert |- ( ph -> ( coeff ` F ) = ( k e. NN0 |-> if ( k <_ N , A , 0 ) ) )

  proof
    wph
    vz
    vk
    cn0
    vk
    cv
    #
    cN
    cle
    wbr
    #
    cA
    cc0
    cif
    #
    cmpt
    #
    cS
    vm
    cF
    cN
    dgrle.1
    dgrle.2
    wph
    vk
    cn0
    @2
    cc
    @3
    wph
    @0
    cn0
    wcel
    #
    wa
    #
    @1
    cA
    cc0
    cc
    @5
    @1
    wa
    #
    wph
    @0
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    cA
    cc
    wcel
    #
    wph
    @4
    @1
    simpll
    @6
    @8
    @1
    @5
    @1
    simpr
    @6
    @0
    cc0
    cuz
    cfv
    #
    wcel
    cN
    cz
    wcel
    #
    @8
    @1
    wb
    @6
    @0
    cn0
    @10
    wph
    @4
    @1
    simplr
    nn0uz
    syl6eleq
    wph
    @11
    @4
    @1
    wph
    cN
    dgrle.2
    nn0zd
    ad2antrr
    @0
    cc0
    cN
    elfz5
    syl2anc
    mpbird
    dgrle.3
    syl2anc
    @5
    @1
    wn
    wa
    0cnd
    ifclda
    #
    @3
    eqid
    #
    fmptd
    #
    wph
    @3
    cN
    c1
    caddc
    co
    cuz
    cfv
    cima
    cc0
    csn
    wceq
    #
    vm
    cv
    #
    @3
    cfv
    #
    cc0
    wne
    #
    @16
    cN
    cle
    wbr
    #
    wi
    #
    vm
    cn0
    wral
    #
    wph
    @0
    @3
    cfv
    #
    cc0
    wne
    #
    @1
    wi
    #
    vk
    cn0
    wral
    @21
    wph
    @24
    vk
    cn0
    @5
    @23
    @2
    cc0
    wne
    @1
    @5
    @22
    @2
    cc0
    @5
    @4
    @2
    cc
    wcel
    #
    @22
    @2
    wceq
    #
    wph
    @4
    simpr
    @12
    vk
    cn0
    @2
    cc
    @3
    @13
    fvmpt2
    #
    syl2anc
    neeq1d
    @1
    @2
    cc0
    @1
    cA
    cc0
    iffalse
    necon1ai
    syl6bi
    ralrimiva
    @24
    @20
    vk
    vm
    cn0
    @24
    vm
    nfv
    @18
    @19
    vk
    vk
    @17
    cc0
    vk
    cn0
    @2
    @16
    nffvmpt1
    #
    vk
    cc0
    nfcv
    nfne
    @19
    vk
    nfv
    nfim
    @0
    @16
    wceq
    #
    @23
    @18
    @1
    @19
    @29
    @22
    @17
    cc0
    @0
    @16
    @3
    fveq2
    #
    neeq1d
    @0
    @16
    cN
    cle
    breq1
    imbi12d
    cbvral
    sylib
    wph
    cN
    cn0
    wcel
    cn0
    cc
    @3
    wf
    @15
    @21
    wb
    dgrle.2
    @14
    @3
    vm
    cN
    plyco0
    syl2anc
    mpbird
    wph
    cF
    vz
    cc
    @7
    cA
    vz
    cv
    #
    @0
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    vz
    cc
    @7
    @17
    @31
    @16
    cexp
    co
    #
    cmul
    co
    #
    vm
    csu
    #
    cmpt
    dgrle.4
    wph
    vz
    cc
    @37
    @34
    wph
    @31
    cc
    wcel
    #
    wa
    #
    @37
    @7
    @22
    @32
    cmul
    co
    #
    vk
    csu
    @34
    @7
    @40
    @36
    vk
    vm
    vm
    @40
    nfcv
    vk
    @17
    @35
    cmul
    @28
    vk
    cmul
    nfcv
    vk
    @35
    nfcv
    nfov
    @29
    @22
    @17
    @32
    @35
    cmul
    @30
    @0
    @16
    @31
    cexp
    oveq2
    oveq12d
    cbvsumi
    @39
    @7
    @40
    @33
    vk
    @39
    @8
    wa
    #
    @22
    cA
    @32
    cmul
    @41
    @22
    @2
    cA
    @41
    @4
    @25
    @26
    @8
    @4
    @39
    @0
    cN
    elfznn0
    adantl
    @41
    @2
    cA
    cc
    @41
    @1
    cA
    cc0
    @8
    @1
    @39
    @0
    cc0
    cN
    elfzle2
    adantl
    iftrued
    #
    wph
    @8
    @9
    @38
    dgrle.3
    adantlr
    eqeltrd
    @27
    syl2anc
    @42
    eqtrd
    oveq1d
    sumeq2dv
    syl5eqr
    mpteq2dva
    eqtr4d
    coeeq
end
