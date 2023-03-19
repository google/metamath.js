include "cvv.mm"
include "cv.mm"
include "wf1.mm"
include "cpw.mm"
include "wrex.mm"
include "cima.mm"
include "cdom.mm"
include "wbr.mm"
include "wral.mm"
include "wcel.mm"
include "wss.mm"
include "elpwi.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "cxp.mm"
include "wi.mm"
include "wb.mm"
include "cfn.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "elpw2g.mm"
include "syl.mm"
include "mpbird.mm"
include "wceq.mm"
include "xpeq2.mm"
include "pweqd.mm"
include "raleqdv.mm"
include "imbi2d.mm"
include "marypha1lem.mm"
include "com12.mm"
include "vtoclga.mm"
include "sylc.mm"
include "imaeq1.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "pweq.mm"
include "rexeqdv.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "mpd.mm"
include "wa.mm"
include "crn.mm"
include "sylan9ssr.mm"
include "rnss.mm"
include "rnxpss.mm"
include "syl6ss.mm"
include "f1ssr.mm"
include "expcom.mm"
include "reximdva.mm"

theorem marypha1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vd: setvar d
  let vb: setvar b
  let vc: setvar c
  assume marypha1.a: |- ( ph -> A e. Fin )
  assume marypha1.b: |- ( ph -> B e. Fin )
  assume marypha1.c: |- ( ph -> C C_ ( A X. B ) )
  assume marypha1.d: |- ( ( ph /\ d C_ A ) -> d ~<_ ( C " d ) )

  disjoint d ph
  disjoint f ph
  disjoint d f
  disjoint A d
  disjoint A f
  disjoint C d
  disjoint C f
  disjoint A b
  disjoint A c
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint c d
  disjoint c f
  disjoint B b
  disjoint B c
  disjoint C c
  assert |- ( ph -> E. f e. ~P C f : A -1-1-> B )

  proof
    wph
    cA
    cvv
    vf
    cv
    #
    wf1
    #
    vf
    cC
    cpw
    #
    wrex
    #
    cA
    cB
    @0
    wf1
    #
    vf
    @2
    wrex
    wph
    vd
    cv
    #
    cC
    @5
    cima
    #
    cdom
    wbr
    #
    vd
    cA
    cpw
    #
    wral
    #
    @3
    wph
    @7
    vd
    @8
    @5
    @8
    wcel
    wph
    @5
    cA
    wss
    @7
    @5
    cA
    elpwi
    marypha1.d
    sylan2
    ralrimiva
    wph
    cC
    cA
    cB
    cxp
    #
    cpw
    #
    wcel
    #
    @5
    vc
    cv
    #
    @5
    cima
    #
    cdom
    wbr
    #
    vd
    @8
    wral
    #
    @1
    vf
    @13
    cpw
    #
    wrex
    #
    wi
    #
    vc
    @11
    wral
    #
    @9
    @3
    wi
    #
    wph
    @12
    cC
    @10
    wss
    #
    marypha1.c
    wph
    @10
    cvv
    wcel
    #
    @12
    @22
    wb
    wph
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    @23
    marypha1.a
    marypha1.b
    cA
    cB
    cfn
    cfn
    xpexg
    syl2anc
    cC
    @10
    cvv
    elpw2g
    syl
    mpbird
    wph
    @25
    @24
    @20
    marypha1.b
    marypha1.a
    @24
    @19
    vc
    cA
    vb
    cv
    #
    cxp
    #
    cpw
    #
    wral
    #
    wi
    @24
    @20
    wi
    vb
    cB
    cfn
    @26
    cB
    wceq
    #
    @29
    @20
    @24
    @30
    @19
    vc
    @28
    @11
    @30
    @27
    @10
    @26
    cB
    cA
    xpeq2
    pweqd
    raleqdv
    imbi2d
    @24
    @26
    cfn
    wcel
    @29
    cA
    vf
    vb
    vc
    vd
    marypha1lem
    com12
    vtoclga
    sylc
    @19
    @21
    vc
    cC
    @11
    @13
    cC
    wceq
    #
    @16
    @9
    @18
    @3
    @31
    @15
    @7
    vd
    @8
    @31
    @14
    @6
    @5
    cdom
    @13
    cC
    @5
    imaeq1
    breq2d
    ralbidv
    @31
    @1
    vf
    @17
    @2
    @13
    cC
    pweq
    rexeqdv
    imbi12d
    rspcva
    syl2anc
    mpd
    wph
    @1
    @4
    vf
    @2
    wph
    @0
    @2
    wcel
    #
    wa
    #
    @0
    crn
    #
    cB
    wss
    #
    @1
    @4
    wi
    @33
    @34
    @10
    crn
    #
    cB
    @33
    @0
    @10
    wss
    @34
    @36
    wss
    @32
    wph
    @0
    cC
    @10
    @0
    cC
    elpwi
    marypha1.c
    sylan9ssr
    @0
    @10
    rnss
    syl
    cA
    cB
    rnxpss
    syl6ss
    @1
    @35
    @4
    cA
    cvv
    cB
    @0
    f1ssr
    expcom
    syl
    reximdva
    mpd
end
