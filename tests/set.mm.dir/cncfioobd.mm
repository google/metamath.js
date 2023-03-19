include "cv.mm"
include "cicc.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cioo.mm"
include "wcel.mm"
include "cc.mm"
include "ccncf.mm"
include "nfv.mm"
include "eqid.mm"
include "cncfiooicc.mm"
include "cniccbdd.mm"
include "syl3anc.mm"
include "wa.mm"
include "nfra1.mm"
include "nfan.mm"
include "cdm.mm"
include "simpr.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "fdm.mm"
include "eqcomd.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "cncfioobdlem.mm"
include "syldan.mm"
include "fveq2d.mm"
include "ad4ant14.mm"
include "simplr.mm"
include "ioossicc.mm"
include "sseldi.mm"
include "rspa.mm"
include "syl2anc.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "reximdva.mm"
include "mpd.mm"

theorem cncfioobd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cL: class L
  let vz: setvar z
  let vk: setvar k
  assume cncfioobd.a: |- ( ph -> A e. RR )
  assume cncfioobd.b: |- ( ph -> B e. RR )
  assume cncfioobd.f: |- ( ph -> F e. ( ( A (,) B ) -cn-> CC ) )
  assume cncfioobd.l: |- ( ph -> L e. ( F limCC B ) )
  assume cncfioobd.r: |- ( ph -> R e. ( F limCC A ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint L x
  disjoint L y
  disjoint R x
  disjoint R y
  disjoint ph x
  disjoint ph y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint F z
  disjoint L z
  disjoint R z
  disjoint ph z
  disjoint k x
  assert |- ( ph -> E. x e. RR A. y e. ( A (,) B ) ( abs ` ( F ` y ) ) <_ x )

  proof
    wph
    vy
    cv
    #
    vz
    cA
    cB
    cicc
    co
    #
    vz
    cv
    #
    cA
    wceq
    cR
    @2
    cB
    wceq
    cL
    @2
    cF
    cfv
    cif
    cif
    cmpt
    #
    cfv
    #
    cabs
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vy
    @1
    wral
    #
    vx
    cr
    wrex
    #
    @0
    cF
    cfv
    #
    cabs
    cfv
    #
    @6
    cle
    wbr
    #
    vy
    cA
    cB
    cioo
    co
    #
    wral
    #
    vx
    cr
    wrex
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @3
    @1
    cc
    ccncf
    co
    wcel
    @9
    cncfioobd.a
    cncfioobd.b
    wph
    vz
    cA
    cB
    cR
    cF
    @3
    cL
    wph
    vz
    nfv
    @3
    eqid
    #
    cncfioobd.a
    cncfioobd.b
    cncfioobd.f
    cncfioobd.l
    cncfioobd.r
    cncfiooicc
    vx
    vy
    cA
    cB
    @3
    cniccbdd
    syl3anc
    wph
    @8
    @14
    vx
    cr
    wph
    @6
    cr
    wcel
    #
    wa
    #
    @8
    @14
    @19
    @8
    wa
    #
    @12
    vy
    @13
    @19
    @8
    vy
    @19
    vy
    nfv
    @7
    vy
    @1
    nfra1
    nfan
    @20
    @0
    @13
    wcel
    #
    @12
    @20
    @21
    wa
    #
    @11
    @5
    @6
    cle
    wph
    @21
    @11
    @5
    wceq
    @18
    @8
    wph
    @21
    wa
    #
    @10
    @4
    cabs
    @23
    @4
    @10
    wph
    @21
    @0
    cF
    cdm
    #
    wcel
    #
    @4
    @10
    wceq
    @23
    @0
    @13
    @24
    wph
    @21
    simpr
    wph
    @13
    @24
    wceq
    @21
    wph
    @24
    @13
    wph
    @13
    cc
    cF
    wf
    #
    @24
    @13
    wceq
    #
    wph
    cF
    @13
    cc
    ccncf
    co
    wcel
    @26
    cncfioobd.f
    @13
    cc
    cF
    cncff
    syl
    #
    @13
    cc
    cF
    fdm
    syl
    #
    eqcomd
    adantr
    eleqtrd
    wph
    @25
    wa
    #
    vz
    cA
    cB
    @0
    cR
    cF
    @3
    cL
    cc
    wph
    @15
    @25
    cncfioobd.a
    adantr
    wph
    @16
    @25
    cncfioobd.b
    adantr
    wph
    @26
    @25
    @28
    adantr
    @17
    @30
    @0
    @24
    @13
    wph
    @25
    simpr
    wph
    @27
    @25
    @29
    adantr
    eleqtrd
    cncfioobdlem
    syldan
    eqcomd
    fveq2d
    ad4ant14
    @22
    @8
    @0
    @1
    wcel
    @7
    @19
    @8
    @21
    simplr
    @22
    @13
    @1
    @0
    cA
    cB
    ioossicc
    @20
    @21
    simpr
    sseldi
    @7
    vy
    @1
    rspa
    syl2anc
    eqbrtrd
    ex
    ralrimi
    ex
    reximdva
    mpd
end
