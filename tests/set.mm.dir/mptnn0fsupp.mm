include "cn0.mm"
include "cmpt.mm"
include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "crab.mm"
include "wfn.mm"
include "cvv.mm"
include "wceq.mm"
include "wral.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "fnmpt.mm"
include "syl.mm"
include "nn0ex.mm"
include "a1i.mm"
include "elex.mm"
include "suppvalfn.mm"
include "syl3anc.mm"
include "clt.mm"
include "wn.mm"
include "wi.mm"
include "wrex.mm"
include "csb.mm"
include "wa.mm"
include "nne.mm"
include "simpr.mm"
include "ad2antrr.mm"
include "rspcsbela.mm"
include "syl2anc.mm"
include "fvmpts.mm"
include "eqeq1d.mm"
include "syl5bb.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "rabssnn0fi.mm"
include "sylibr.mm"
include "eqeltrd.mm"
include "wfun.mm"
include "wb.mm"
include "funmpt.mm"
include "mptex.mm"
include "funisfsupp.mm"

theorem mptnn0fsupp
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
  assume mptnn0fsupp.s: |- ( ph -> E. s e. NN0 A. x e. NN0 ( s < x -> [_ x / k ]_ C = .0. ) )

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
  assert |- ( ph -> ( k e. NN0 |-> C ) finSupp .0. )

  proof
    wph
    vk
    cn0
    cC
    cmpt
    #
    c.0
    cfsupp
    wbr
    #
    @0
    c.0
    csupp
    co
    #
    cfn
    wcel
    #
    wph
    @2
    vx
    cv
    #
    @0
    cfv
    #
    c.0
    wne
    #
    vx
    cn0
    crab
    #
    cfn
    wph
    @0
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
    @2
    @7
    wceq
    wph
    cC
    cB
    wcel
    #
    vk
    cn0
    wral
    #
    @8
    wph
    @11
    vk
    cn0
    mptnn0fsupp.c
    ralrimiva
    #
    vk
    cn0
    cC
    @0
    cB
    @0
    eqid
    #
    fnmpt
    syl
    @9
    wph
    nn0ex
    a1i
    wph
    c.0
    cV
    wcel
    @10
    mptnn0fsupp.0
    c.0
    cV
    elex
    syl
    #
    vx
    @0
    cvv
    cvv
    cn0
    c.0
    suppvalfn
    syl3anc
    wph
    vs
    cv
    #
    @4
    clt
    wbr
    #
    @6
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
    #
    @7
    cfn
    wcel
    wph
    @21
    @17
    vk
    @4
    cC
    csb
    #
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
    mptnn0fsupp.s
    wph
    @20
    @25
    vs
    cn0
    wph
    @16
    cn0
    wcel
    #
    wa
    #
    @19
    @24
    vx
    cn0
    @27
    @4
    cn0
    wcel
    #
    wa
    #
    @18
    @23
    @17
    @18
    @5
    c.0
    wceq
    @29
    @23
    @5
    c.0
    nne
    @29
    @5
    @22
    c.0
    @29
    @28
    @22
    cB
    wcel
    #
    @5
    @22
    wceq
    @27
    @28
    simpr
    #
    @29
    @28
    @12
    @30
    @31
    wph
    @12
    @26
    @28
    @13
    ad2antrr
    vk
    @4
    cn0
    cC
    cB
    rspcsbela
    syl2anc
    vk
    @4
    cC
    cn0
    @0
    cB
    @14
    fvmpts
    syl2anc
    eqeq1d
    syl5bb
    imbi2d
    ralbidva
    rexbidva
    mpbird
    @6
    vx
    vs
    rabssnn0fi
    sylibr
    eqeltrd
    wph
    @0
    wfun
    #
    @0
    cvv
    wcel
    #
    @10
    @1
    @3
    wb
    @32
    wph
    vk
    cn0
    cC
    funmpt
    a1i
    @33
    wph
    vk
    cn0
    cC
    nn0ex
    mptex
    a1i
    @15
    @0
    cvv
    cvv
    c.0
    funisfsupp
    syl3anc
    mpbird
end
