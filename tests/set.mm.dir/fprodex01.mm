include "c1.mm"
include "wceq.mm"
include "wral.mm"
include "cc0.mm"
include "cif.mm"
include "cprod.mm"
include "wa.mm"
include "simpr.mm"
include "cv.mm"
include "eqeq1d.mm"
include "cbvralv.mm"
include "sylibr.mm"
include "prodeq2d.mm"
include "cfn.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "prod1.mm"
include "olcs.mm"
include "syl.mm"
include "adantr.mm"
include "eqtr2d.mm"
include "wn.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfn.mm"
include "nfan.mm"
include "ad2antrr.mm"
include "cc.mm"
include "cpr.mm"
include "cr.mm"
include "pr01ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "sseldi.mm"
include "adantlr.mm"
include "simplr.mm"
include "fprodeq02.mm"
include "wrex.mm"
include "rexnal.mm"
include "biimpri.mm"
include "adantl.mm"
include "wi.mm"
include "wo.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "c0ex.mm"
include "1ex.mm"
include "elpr2.mm"
include "orcomd.mm"
include "ord.mm"
include "reximdva.mm"
include "mpd.mm"
include "r19.29af2.mm"
include "eqcomd.mm"
include "ifeqda.mm"

theorem fprodex01
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vl: setvar l
  assume fprodex01.1: |- ( k = l -> B = C )
  assume fprodex01.a: |- ( ph -> A e. Fin )
  assume fprodex01.b: |- ( ( ph /\ k e. A ) -> B e. { 0 , 1 } )

  disjoint A k
  disjoint A l
  disjoint k l
  disjoint B l
  disjoint C k
  disjoint k ph
  disjoint l ph
  assert |- ( ph -> prod_ k e. A B = if ( A. l e. A C = 1 , 1 , 0 ) )

  proof
    wph
    cC
    c1
    wceq
    #
    vl
    cA
    wral
    #
    c1
    cc0
    cif
    cA
    cB
    vk
    cprod
    #
    wph
    @1
    c1
    cc0
    @2
    wph
    @1
    wa
    #
    @2
    cA
    c1
    vk
    cprod
    #
    c1
    @3
    cA
    cB
    c1
    vk
    @3
    @1
    cB
    c1
    wceq
    #
    vk
    cA
    wral
    wph
    @1
    simpr
    @5
    @0
    vk
    vl
    cA
    vk
    cv
    #
    vl
    cv
    #
    wceq
    #
    cB
    cC
    c1
    fprodex01.1
    eqeq1d
    cbvralv
    sylibr
    prodeq2d
    wph
    @4
    c1
    wceq
    #
    @1
    wph
    cA
    cfn
    wcel
    #
    @9
    fprodex01.a
    cA
    cc0
    cuz
    cfv
    wss
    @10
    @9
    cA
    vk
    cc0
    prod1
    olcs
    syl
    adantr
    eqtr2d
    wph
    @1
    wn
    #
    wa
    #
    @2
    cc0
    @12
    cC
    cc0
    wceq
    #
    @2
    cc0
    wceq
    #
    vl
    cA
    wph
    @11
    vl
    wph
    vl
    nfv
    @1
    vl
    @0
    vl
    cA
    nfra1
    nfn
    nfan
    @14
    vl
    nfv
    @12
    @7
    cA
    wcel
    #
    wa
    #
    @13
    wa
    cA
    cB
    cC
    vk
    @7
    fprodex01.1
    @12
    @10
    @15
    @13
    wph
    @10
    @11
    fprodex01.a
    adantr
    ad2antrr
    @16
    @6
    cA
    wcel
    #
    cB
    cc
    wcel
    #
    @13
    @12
    @17
    @18
    @15
    wph
    @17
    @18
    @11
    wph
    @17
    wa
    cc0
    c1
    cpr
    #
    cc
    cB
    @19
    cr
    cc
    pr01ssre
    ax-resscn
    sstri
    fprodex01.b
    sseldi
    adantlr
    adantlr
    adantlr
    @12
    @15
    @13
    simplr
    @16
    @13
    simpr
    fprodeq02
    @12
    @0
    wn
    #
    vl
    cA
    wrex
    #
    @13
    vl
    cA
    wrex
    #
    @11
    @21
    wph
    @21
    @11
    @0
    vl
    cA
    rexnal
    biimpri
    adantl
    wph
    @21
    @22
    wi
    @11
    wph
    @20
    @13
    vl
    cA
    wph
    @15
    wa
    #
    @0
    @13
    @23
    @13
    @0
    @23
    cC
    @19
    wcel
    #
    @13
    @0
    wo
    wph
    @24
    vl
    cA
    wph
    cB
    @19
    wcel
    #
    vk
    cA
    wral
    @24
    vl
    cA
    wral
    wph
    @25
    vk
    cA
    fprodex01.b
    ralrimiva
    @25
    @24
    vk
    vl
    cA
    @8
    cB
    cC
    @19
    fprodex01.1
    eleq1d
    cbvralv
    sylib
    r19.21bi
    cC
    cc0
    c1
    c0ex
    1ex
    elpr2
    sylib
    orcomd
    ord
    reximdva
    adantr
    mpd
    r19.29af2
    eqcomd
    ifeqda
    eqcomd
end
