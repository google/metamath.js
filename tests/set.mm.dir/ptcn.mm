include "cmpt.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cuni.mm"
include "wf.mm"
include "cv.mm"
include "ccnp.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "cixp.mm"
include "ctopon.mm"
include "adantr.mm"
include "ctop.mm"
include "ffvelrnda.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "an32s.mm"
include "ralrimiva.mm"
include "wb.mm"
include "mptelixpg.mm"
include "syl.mm"
include "mpbird.mm"
include "wceq.mm"
include "ptuni.mm"
include "syl2anc.mm"
include "eleqtrd.mm"
include "fmptd.mm"
include "simpr.mm"
include "adantlr.mm"
include "simplr.mm"
include "toponuni.mm"
include "ad2antrr.mm"
include "cncnpi.mm"
include "ptcnp.mm"
include "cpt.mm"
include "pttop.mm"
include "syl5eqel.mm"
include "cncnp.mm"
include "mpbir2and.mm"

theorem ptcn
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let cX: class X
  let vz: setvar z
  assume ptcn.2: |- K = ( Xt_ ` F )
  assume ptcn.3: |- ( ph -> J e. ( TopOn ` X ) )
  assume ptcn.4: |- ( ph -> I e. V )
  assume ptcn.5: |- ( ph -> F : I --> Top )
  assume ptcn.6: |- ( ( ph /\ k e. I ) -> ( x e. X |-> A ) e. ( J Cn ( F ` k ) ) )

  disjoint k x
  disjoint F k
  disjoint F x
  disjoint I k
  disjoint I x
  disjoint J k
  disjoint k ph
  disjoint ph x
  disjoint X k
  disjoint X x
  disjoint K x
  disjoint V k
  disjoint V x
  disjoint k z
  disjoint x z
  disjoint I z
  disjoint J z
  disjoint ph z
  disjoint X z
  disjoint A z
  disjoint K z
  assert |- ( ph -> ( x e. X |-> ( k e. I |-> A ) ) e. ( J Cn K ) )

  proof
    wph
    vx
    cX
    vk
    cI
    cA
    cmpt
    #
    cmpt
    #
    cJ
    cK
    ccn
    co
    wcel
    #
    cX
    cK
    cuni
    #
    @1
    wf
    #
    @1
    vz
    cv
    #
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    vz
    cX
    wral
    #
    wph
    vx
    cX
    @0
    @3
    @1
    wph
    vx
    cv
    cX
    wcel
    #
    wa
    #
    @0
    vk
    cI
    vk
    cv
    #
    cF
    cfv
    #
    cuni
    #
    cixp
    #
    @3
    @9
    @0
    @13
    wcel
    #
    cA
    @12
    wcel
    #
    vk
    cI
    wral
    #
    @9
    @15
    vk
    cI
    wph
    @10
    cI
    wcel
    #
    @8
    @15
    wph
    @17
    wa
    #
    @15
    vx
    cX
    @18
    cX
    @12
    vx
    cX
    cA
    cmpt
    #
    wf
    #
    @15
    vx
    cX
    wral
    @18
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @11
    @12
    ctopon
    cfv
    wcel
    #
    @19
    cJ
    @11
    ccn
    co
    wcel
    #
    @20
    wph
    @21
    @17
    ptcn.3
    adantr
    @18
    @11
    ctop
    wcel
    @22
    wph
    cI
    ctop
    @10
    cF
    ptcn.5
    ffvelrnda
    @11
    @12
    @12
    eqid
    toptopon
    sylib
    ptcn.6
    @19
    cJ
    @11
    cX
    @12
    cnf2
    syl3anc
    vx
    cX
    @12
    cA
    @19
    @19
    eqid
    fmpt
    sylibr
    r19.21bi
    an32s
    ralrimiva
    @9
    cI
    cV
    wcel
    #
    @14
    @16
    wb
    wph
    @24
    @8
    ptcn.4
    adantr
    vk
    cI
    cA
    @12
    cV
    mptelixpg
    syl
    mpbird
    wph
    @13
    @3
    wceq
    #
    @8
    wph
    @24
    cI
    ctop
    cF
    wf
    #
    @25
    ptcn.4
    ptcn.5
    vk
    cI
    cF
    cK
    cV
    ptcn.2
    ptuni
    syl2anc
    adantr
    eleqtrd
    @1
    eqid
    fmptd
    wph
    @6
    vz
    cX
    wph
    @5
    cX
    wcel
    #
    wa
    #
    vx
    cA
    @5
    vk
    cF
    cI
    cJ
    cK
    cV
    cX
    ptcn.2
    wph
    @21
    @27
    ptcn.3
    adantr
    wph
    @24
    @27
    ptcn.4
    adantr
    wph
    @26
    @27
    ptcn.5
    adantr
    wph
    @27
    simpr
    @28
    @17
    wa
    #
    @23
    @5
    cJ
    cuni
    #
    wcel
    @19
    @5
    cJ
    @11
    ccnp
    co
    cfv
    wcel
    wph
    @17
    @23
    @27
    ptcn.6
    adantlr
    @29
    @5
    cX
    @30
    wph
    @27
    @17
    simplr
    wph
    cX
    @30
    wceq
    #
    @27
    @17
    wph
    @21
    @31
    ptcn.3
    cX
    cJ
    toponuni
    syl
    ad2antrr
    eleqtrd
    @5
    @19
    cJ
    @11
    @30
    @30
    eqid
    cncnpi
    syl2anc
    ptcnp
    ralrimiva
    wph
    @21
    cK
    @3
    ctopon
    cfv
    wcel
    #
    @2
    @4
    @7
    wa
    wb
    ptcn.3
    wph
    cK
    ctop
    wcel
    @32
    wph
    cK
    cF
    cpt
    cfv
    #
    ctop
    ptcn.2
    wph
    @24
    @26
    @33
    ctop
    wcel
    ptcn.4
    ptcn.5
    cI
    cF
    cV
    pttop
    syl2anc
    syl5eqel
    cK
    @3
    @3
    eqid
    toptopon
    sylib
    vz
    @1
    cJ
    cK
    cX
    @3
    cncnp
    syl2anc
    mpbir2and
end
