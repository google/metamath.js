include "cfv.mm"
include "cesum.mm"
include "nfv.mm"
include "nfcv.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "ccn.mm"
include "cxrs.mm"
include "cress.mm"
include "ctps.mm"
include "cuni.mm"
include "wceq.mm"
include "xrge0tps.mm"
include "xrge0base.mm"
include "cle.mm"
include "cordt.mm"
include "crest.mm"
include "ctopn.mm"
include "xrge0topn.mm"
include "eqtr4i.mm"
include "tpsuni.mm"
include "ax-mp.mm"
include "cnf.mm"
include "syl.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "cmpt.mm"
include "ccom.mm"
include "ctsu.mm"
include "ccmn.mm"
include "xrge0cmn.mm"
include "a1i.mm"
include "cmnd.mm"
include "cxad.mm"
include "wral.mm"
include "cmhm.mm"
include "cmnmnd.mm"
include "3expib.mm"
include "ralrimivv.mm"
include "w3a.mm"
include "xrge0plusg.mm"
include "xrge00.mm"
include "ismhm.mm"
include "biimpri.mm"
include "syl23anc.mm"
include "eqidd.mm"
include "fmpt3d.mm"
include "esumel.mm"
include "tsmsmhm.mm"
include "cofmpt.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "esumid.mm"
include "eqcomd.mm"

theorem esumcocn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cJ: class J
  let cV: class V
  assume esumcocn.j: |- J = ( ( ordTop ` <_ ) |`t ( 0 [,] +oo ) )
  assume esumcocn.a: |- ( ph -> A e. V )
  assume esumcocn.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume esumcocn.1: |- ( ph -> C e. ( J Cn J ) )
  assume esumcocn.0: |- ( ph -> ( C ` 0 ) = 0 )
  assume esumcocn.f: |- ( ( ph /\ x e. ( 0 [,] +oo ) /\ y e. ( 0 [,] +oo ) ) -> ( C ` ( x +e y ) ) = ( ( C ` x ) +e ( C ` y ) ) )

  disjoint A k
  disjoint x y
  disjoint k x
  disjoint C x
  disjoint k y
  disjoint C y
  disjoint C k
  disjoint V k
  disjoint ph x
  disjoint ph y
  disjoint k ph
  assert |- ( ph -> ( C ` sum* k e. A B ) = sum* k e. A ( C ` B ) )

  proof
    wph
    cA
    cB
    cC
    cfv
    #
    vk
    cesum
    cA
    cB
    vk
    cesum
    #
    cC
    cfv
    #
    wph
    cA
    @0
    @2
    vk
    cV
    wph
    vk
    nfv
    #
    vk
    cA
    nfcv
    #
    esumcocn.a
    wph
    vk
    cv
    cA
    wcel
    #
    wa
    cc0
    cpnf
    cicc
    co
    #
    @6
    cB
    cC
    wph
    @6
    @6
    cC
    wf
    #
    @5
    wph
    cC
    cJ
    cJ
    ccn
    co
    wcel
    @7
    esumcocn.1
    cC
    cJ
    cJ
    @6
    @6
    cxrs
    @6
    cress
    co
    #
    ctps
    wcel
    #
    @6
    cJ
    cuni
    wceq
    xrge0tps
    @6
    cJ
    @8
    xrge0base
    cJ
    cle
    cordt
    cfv
    @6
    crest
    co
    @8
    ctopn
    cfv
    esumcocn.j
    xrge0topn
    eqtr4i
    #
    tpsuni
    ax-mp
    #
    @11
    cnf
    syl
    #
    adantr
    esumcocn.b
    ffvelrnd
    wph
    @2
    @8
    cC
    vk
    cA
    cB
    cmpt
    #
    ccom
    #
    ctsu
    co
    @8
    vk
    cA
    @0
    cmpt
    #
    ctsu
    co
    wph
    cA
    @6
    cC
    @13
    @8
    @8
    cJ
    cJ
    cV
    @1
    xrge0base
    @10
    @10
    @8
    ccmn
    wcel
    #
    wph
    xrge0cmn
    a1i
    #
    @9
    wph
    xrge0tps
    a1i
    #
    @17
    @18
    wph
    @8
    cmnd
    wcel
    #
    @19
    @7
    vx
    cv
    #
    vy
    cv
    #
    cxad
    co
    cC
    cfv
    @20
    cC
    cfv
    @21
    cC
    cfv
    cxad
    co
    wceq
    #
    vy
    @6
    wral
    vx
    @6
    wral
    #
    cc0
    cC
    cfv
    cc0
    wceq
    #
    cC
    @8
    @8
    cmhm
    co
    wcel
    #
    @19
    wph
    @16
    @19
    xrge0cmn
    @8
    cmnmnd
    ax-mp
    a1i
    #
    @26
    @12
    wph
    @22
    vx
    vy
    @6
    @6
    wph
    @20
    @6
    wcel
    @21
    @6
    wcel
    @22
    esumcocn.f
    3expib
    ralrimivv
    esumcocn.0
    @25
    @19
    @19
    wa
    @7
    @23
    @24
    w3a
    wa
    vx
    vy
    @6
    @6
    cxad
    cxad
    @8
    @8
    cC
    cc0
    cc0
    xrge0base
    xrge0base
    xrge0plusg
    xrge0plusg
    xrge00
    xrge00
    ismhm
    biimpri
    syl23anc
    esumcocn.1
    esumcocn.a
    wph
    vk
    cA
    cB
    @6
    @13
    wph
    @13
    eqidd
    esumcocn.b
    fmpt3d
    wph
    cA
    cB
    vk
    cV
    @3
    @4
    esumcocn.a
    esumcocn.b
    esumel
    tsmsmhm
    wph
    @14
    @15
    @8
    ctsu
    wph
    vk
    cA
    cB
    @6
    @6
    cC
    @12
    esumcocn.b
    cofmpt
    oveq2d
    eleqtrd
    esumid
    eqcomd
end
