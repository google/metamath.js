include "cmpt.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cv.mm"
include "cneg.mm"
include "wcel.mm"
include "crab.mm"
include "cinf.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wceq.mm"
include "eqid.mm"
include "rnmptssd.mm"
include "rnmptn0.mm"
include "rnmptbd.mm"
include "mpbid.mm"
include "supminf.mm"
include "syl3anc.mm"
include "wi.mm"
include "wa.mm"
include "simpr.mm"
include "wb.mm"
include "renegcl.mm"
include "elrnmpt.mm"
include "syl.mm"
include "adantr.mm"
include "adantll.mm"
include "nfv.mm"
include "nfan.mm"
include "negeq.mm"
include "eqcomd.mm"
include "adantl.mm"
include "recn.mm"
include "negnegd.mm"
include "eqtr2d.mm"
include "ex.mm"
include "recnd.mm"
include "eqtrd.mm"
include "adantlr.mm"
include "impbid.mm"
include "rexbida.mm"
include "simplr.mm"
include "elrnmptd.mm"
include "ralrimiva.mm"
include "rabss.mm"
include "sylibr.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel.mm"
include "nfrab.mm"
include "eleq1d.mm"
include "renegcld.mm"
include "elrnmpt1.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "elrabd.mm"
include "rnmptssdf.mm"
include "eqssd.mm"
include "infeq1d.mm"
include "negeqd.mm"

theorem supminfrnmpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  assume supminfrnmpt.x: |- F/ x ph
  assume supminfrnmpt.a: |- ( ph -> A =/= (/) )
  assume supminfrnmpt.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume supminfrnmpt.y: |- ( ph -> E. y e. RR A. x e. A B <_ y )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint A w
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint B w
  disjoint B z
  disjoint ph w
  assert |- ( ph -> sup ( ran ( x e. A |-> B ) , RR , < ) = -u inf ( ran ( x e. A |-> -u B ) , RR , < ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    vw
    cv
    #
    cneg
    #
    @1
    wcel
    #
    vw
    cr
    crab
    #
    cr
    clt
    cinf
    #
    cneg
    #
    vx
    cA
    cB
    cneg
    #
    cmpt
    #
    crn
    #
    cr
    clt
    cinf
    #
    cneg
    wph
    @1
    cr
    wss
    @1
    c0
    wne
    vz
    cv
    vy
    cv
    #
    cle
    wbr
    vz
    @1
    wral
    vy
    cr
    wrex
    #
    @2
    @8
    wceq
    wph
    vx
    cA
    cB
    cr
    @0
    supminfrnmpt.x
    @0
    eqid
    #
    supminfrnmpt.b
    rnmptssd
    wph
    vx
    cA
    cB
    @0
    cr
    supminfrnmpt.x
    supminfrnmpt.b
    @15
    supminfrnmpt.a
    rnmptn0
    wph
    cB
    @13
    cle
    wbr
    vx
    cA
    wral
    vy
    cr
    wrex
    @14
    supminfrnmpt.y
    wph
    vx
    vy
    vz
    cA
    cB
    cr
    supminfrnmpt.x
    supminfrnmpt.b
    rnmptbd
    mpbid
    vy
    vz
    vw
    @1
    supminf
    syl3anc
    wph
    @7
    @12
    wph
    cr
    @6
    @11
    clt
    wph
    @6
    @11
    wph
    @5
    @3
    @11
    wcel
    #
    wi
    #
    vw
    cr
    wral
    @6
    @11
    wss
    wph
    @17
    vw
    cr
    wph
    @3
    cr
    wcel
    #
    wa
    #
    @5
    @16
    @19
    @5
    wa
    #
    vx
    cA
    @9
    @3
    @10
    cr
    @10
    eqid
    #
    @20
    @4
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @3
    @9
    wceq
    #
    vx
    cA
    wrex
    #
    @18
    @5
    @23
    wph
    @18
    @5
    wa
    @5
    @23
    @18
    @5
    simpr
    @18
    @5
    @23
    wb
    #
    @5
    @18
    @4
    cr
    wcel
    @26
    @3
    renegcl
    vx
    cA
    cB
    @4
    @0
    cr
    @15
    elrnmpt
    syl
    adantr
    mpbid
    adantll
    @19
    @23
    @25
    wb
    @5
    @19
    @22
    @24
    vx
    cA
    wph
    @18
    vx
    supminfrnmpt.x
    @18
    vx
    nfv
    nfan
    @19
    vx
    cv
    cA
    wcel
    #
    wa
    @22
    @24
    @19
    @22
    @24
    wi
    #
    @27
    @18
    @28
    wph
    @18
    @22
    @24
    @18
    @22
    wa
    @9
    @4
    cneg
    #
    @3
    @22
    @9
    @29
    wceq
    @18
    @22
    @29
    @9
    @4
    cB
    negeq
    eqcomd
    adantl
    @18
    @29
    @3
    wceq
    @22
    @18
    @3
    @3
    recn
    negnegd
    adantr
    eqtr2d
    ex
    adantl
    adantr
    wph
    @27
    @24
    @22
    wi
    @18
    wph
    @27
    wa
    #
    @24
    @22
    @30
    @24
    wa
    @4
    @9
    cneg
    #
    cB
    @24
    @4
    @31
    wceq
    @30
    @3
    @9
    negeq
    #
    adantl
    @30
    @31
    cB
    wceq
    @24
    @30
    cB
    @30
    cB
    supminfrnmpt.b
    recnd
    negnegd
    #
    adantr
    eqtrd
    ex
    adantlr
    impbid
    rexbida
    adantr
    mpbid
    wph
    @18
    @5
    simplr
    elrnmptd
    ex
    ralrimiva
    @5
    vw
    cr
    @11
    rabss
    sylibr
    wph
    vx
    cA
    @9
    @6
    @10
    supminfrnmpt.x
    @5
    vx
    vw
    cr
    vx
    @4
    @1
    vx
    @4
    nfcv
    vx
    @0
    vx
    cA
    cB
    nfmpt1
    nfrn
    nfel
    vx
    cr
    nfcv
    nfrab
    @21
    @30
    @5
    @31
    @1
    wcel
    vw
    @9
    cr
    @24
    @4
    @31
    @1
    @32
    eleq1d
    @30
    cB
    supminfrnmpt.b
    renegcld
    @30
    @31
    cB
    @1
    @33
    @30
    @27
    cB
    cr
    wcel
    cB
    @1
    wcel
    wph
    @27
    simpr
    supminfrnmpt.b
    vx
    cA
    cB
    @0
    cr
    @15
    elrnmpt1
    syl2anc
    eqeltrd
    elrabd
    rnmptssdf
    eqssd
    infeq1d
    negeqd
    eqtrd
end
