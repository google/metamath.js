include "cv.mm"
include "csb.mm"
include "wne.mm"
include "cn0.mm"
include "crab.mm"
include "cfn.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cmpt.mm"
include "cfsupp.mm"
include "wfun.mm"
include "csupp.mm"
include "co.mm"
include "wa.mm"
include "fsuppimp.mm"
include "cfv.mm"
include "wfn.mm"
include "cvv.mm"
include "w3a.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "fnmpt.mm"
include "syl.mm"
include "nn0ex.mm"
include "a1i.mm"
include "elex.mm"
include "3jca.mm"
include "adantr.mm"
include "suppvalfn.mm"
include "simpr.mm"
include "rspcsbela.mm"
include "syl2anc.mm"
include "fvmpts.mm"
include "neeq1d.mm"
include "rabbidva.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "expcom.mm"
include "com23.mm"
include "imp.mm"
include "mpcom.mm"
include "wn.mm"
include "rabssnn0fi.mm"
include "nne.mm"
include "imbi2i.mm"
include "ralbii.mm"
include "rexbii.mm"
include "bitri.mm"
include "sylib.mm"

theorem mptnn0fsuppr
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  let c.0: class .0.
  let vs: setvar s
  assume mptnn0fsupp.0: |- ( ph -> .0. e. V )
  assume mptnn0fsupp.c: |- ( ( ph /\ k e. NN0 ) -> C e. B )
  assume mptnn0fsuppr.s: |- ( ph -> ( k e. NN0 |-> C ) finSupp .0. )

  disjoint B k
  disjoint C s
  disjoint C x
  disjoint s x
  disjoint k ph
  disjoint ph s
  disjoint ph x
  disjoint k s
  disjoint k x
  disjoint .0. s
  disjoint .0. x
  assert |- ( ph -> E. s e. NN0 A. x e. NN0 ( s < x -> [_ x / k ]_ C = .0. ) )

  proof
    wph
    vk
    vx
    cv
    #
    cC
    csb
    #
    c.0
    wne
    #
    vx
    cn0
    crab
    #
    cfn
    wcel
    #
    vs
    cv
    @0
    clt
    wbr
    #
    @1
    c.0
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vs
    cn0
    wrex
    #
    vk
    cn0
    cC
    cmpt
    #
    c.0
    cfsupp
    wbr
    #
    wph
    @4
    mptnn0fsuppr.s
    @11
    @10
    wfun
    #
    @10
    c.0
    csupp
    co
    #
    cfn
    wcel
    #
    wa
    wph
    @4
    wi
    #
    @10
    c.0
    fsuppimp
    @12
    @14
    @15
    @12
    wph
    @14
    @4
    wph
    @12
    @14
    @4
    wi
    wph
    @12
    wa
    #
    @14
    @4
    @16
    @13
    @3
    cfn
    @16
    @13
    @0
    @10
    cfv
    #
    c.0
    wne
    #
    vx
    cn0
    crab
    #
    @3
    @16
    @10
    cn0
    wfn
    #
    cn0
    cvv
    wcel
    #
    c.0
    cvv
    wcel
    #
    w3a
    #
    @13
    @19
    wceq
    wph
    @23
    @12
    wph
    @20
    @21
    @22
    wph
    cC
    cB
    wcel
    #
    vk
    cn0
    wral
    #
    @20
    wph
    @24
    vk
    cn0
    mptnn0fsupp.c
    ralrimiva
    #
    vk
    cn0
    cC
    @10
    cB
    @10
    eqid
    #
    fnmpt
    syl
    @21
    wph
    nn0ex
    a1i
    wph
    c.0
    cV
    wcel
    @22
    mptnn0fsupp.0
    c.0
    cV
    elex
    syl
    3jca
    adantr
    vx
    @10
    cvv
    cvv
    cn0
    c.0
    suppvalfn
    syl
    @16
    @18
    @2
    vx
    cn0
    @16
    @0
    cn0
    wcel
    #
    wa
    #
    @17
    @1
    c.0
    @29
    @28
    @1
    cB
    wcel
    #
    @17
    @1
    wceq
    @16
    @28
    simpr
    #
    @29
    @28
    @25
    @30
    @31
    @16
    @25
    @28
    wph
    @25
    @12
    @26
    adantr
    adantr
    vk
    @0
    cn0
    cC
    cB
    rspcsbela
    syl2anc
    vk
    @0
    cC
    cn0
    @10
    cB
    @27
    fvmpts
    syl2anc
    neeq1d
    rabbidva
    eqtrd
    eleq1d
    biimpd
    expcom
    com23
    imp
    syl
    mpcom
    @4
    @5
    @2
    wn
    #
    wi
    #
    vx
    cn0
    wral
    #
    vs
    cn0
    wrex
    @9
    @2
    vx
    vs
    rabssnn0fi
    @34
    @8
    vs
    cn0
    @33
    @7
    vx
    cn0
    @32
    @6
    @5
    @1
    c.0
    nne
    imbi2i
    ralbii
    rexbii
    bitri
    sylib
end
