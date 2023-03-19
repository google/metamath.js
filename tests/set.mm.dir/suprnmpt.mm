include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wrex.mm"
include "ralrimiva.mm"
include "rnmptss.mm"
include "syl.mm"
include "nfv.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfrn.mm"
include "nfcv.mm"
include "nfne.mm"
include "wex.mm"
include "n0.mm"
include "sylib.mm"
include "wa.mm"
include "simpr.mm"
include "elrnmpt1.mm"
include "syl2anc.mm"
include "ne0i.mm"
include "exlimdd.mm"
include "nfre1.mm"
include "w3a.mm"
include "simp2.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl3.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "adantl.mm"
include "simp3.mm"
include "nfra1.mm"
include "nf3an.mm"
include "wi.mm"
include "rspa.mm"
include "3adant3.mm"
include "eqbrtrd.mm"
include "3exp.mm"
include "3ad2ant2.mm"
include "rexlimd.mm"
include "mpd.mm"
include "syl3anc.mm"
include "19.8a.mm"
include "df-rex.mm"
include "sylibr.mm"
include "suprcl.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "suprub.mm"
include "syl31anc.mm"
include "syl6breqr.mm"
include "jca.mm"

theorem suprnmpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vz: setvar z
  assume suprnmpt.a: |- ( ph -> A =/= (/) )
  assume suprnmpt.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume suprnmpt.bnd: |- ( ph -> E. y e. RR A. x e. A B <_ y )
  assume suprnmpt.f: |- F = ( x e. A |-> B )
  assume suprnmpt.c: |- C = sup ( ran F , RR , < )

  disjoint A x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint A z
  disjoint x z
  disjoint B z
  disjoint F z
  disjoint y z
  disjoint ph z
  assert |- ( ph -> ( C e. RR /\ A. x e. A B <_ C ) )

  proof
    wph
    cC
    cr
    wcel
    cB
    cC
    cle
    wbr
    #
    vx
    cA
    wral
    wph
    cC
    cF
    crn
    #
    cr
    clt
    csup
    #
    cr
    suprnmpt.c
    wph
    @1
    cr
    wss
    #
    @1
    c0
    wne
    #
    vz
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vz
    @1
    wral
    #
    vy
    cr
    wrex
    #
    @2
    cr
    wcel
    wph
    cB
    cr
    wcel
    #
    vx
    cA
    wral
    @3
    wph
    @10
    vx
    cA
    suprnmpt.b
    ralrimiva
    vx
    cA
    cB
    cr
    cF
    suprnmpt.f
    rnmptss
    syl
    #
    wph
    vx
    cv
    cA
    wcel
    #
    @4
    vx
    wph
    vx
    nfv
    #
    vx
    @1
    c0
    vx
    cF
    vx
    cF
    vx
    cA
    cB
    cmpt
    suprnmpt.f
    vx
    cA
    cB
    nfmpt1
    nfcxfr
    nfrn
    vx
    c0
    nfcv
    nfne
    wph
    cA
    c0
    wne
    @12
    vx
    wex
    suprnmpt.a
    vx
    cA
    n0
    sylib
    wph
    @12
    wa
    #
    cB
    @1
    wcel
    #
    @4
    @14
    @12
    @10
    @15
    wph
    @12
    simpr
    suprnmpt.b
    vx
    cA
    cB
    cF
    cr
    suprnmpt.f
    elrnmpt1
    syl2anc
    #
    @1
    cB
    ne0i
    syl
    #
    exlimdd
    wph
    cB
    @6
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vy
    cr
    wrex
    @9
    suprnmpt.bnd
    wph
    @19
    @9
    vy
    cr
    wph
    vy
    nfv
    @8
    vy
    cr
    nfre1
    wph
    @6
    cr
    wcel
    #
    @19
    @9
    wph
    @20
    @19
    w3a
    #
    @20
    @8
    wa
    #
    vy
    wex
    #
    @9
    @21
    @20
    @8
    @23
    wph
    @20
    @19
    simp2
    @21
    @7
    vz
    @1
    @21
    @5
    @1
    wcel
    #
    wa
    wph
    @19
    @5
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @7
    wph
    @20
    @19
    @24
    simpl1
    wph
    @20
    @19
    @24
    simpl3
    @24
    @26
    @21
    @24
    @26
    @5
    cvv
    wcel
    @24
    @26
    wb
    vz
    vex
    vx
    cA
    cB
    @5
    cF
    cvv
    suprnmpt.f
    elrnmpt
    ax-mp
    biimpi
    adantl
    wph
    @19
    @26
    w3a
    #
    @26
    @7
    wph
    @19
    @26
    simp3
    @27
    @25
    @7
    vx
    cA
    wph
    @19
    @26
    vx
    @13
    @18
    vx
    cA
    nfra1
    @25
    vx
    cA
    nfre1
    nf3an
    @7
    vx
    nfv
    @19
    wph
    @12
    @25
    @7
    wi
    wi
    @26
    @19
    @12
    @25
    @7
    @19
    @12
    @25
    w3a
    @5
    cB
    @6
    cle
    @19
    @12
    @25
    simp3
    @19
    @12
    @18
    @25
    @18
    vx
    cA
    rspa
    3adant3
    eqbrtrd
    3exp
    3ad2ant2
    rexlimd
    mpd
    syl3anc
    ralrimiva
    @22
    vy
    19.8a
    syl2anc
    @8
    vy
    cr
    df-rex
    sylibr
    3exp
    rexlimd
    mpd
    #
    vy
    vz
    @1
    suprcl
    syl3anc
    syl5eqel
    wph
    @0
    vx
    cA
    @14
    cB
    @2
    cC
    cle
    @14
    @3
    @4
    @9
    @15
    cB
    @2
    cle
    wbr
    wph
    @3
    @12
    @11
    adantr
    @17
    wph
    @9
    @12
    @28
    adantr
    @16
    vy
    vz
    @1
    cB
    suprub
    syl31anc
    suprnmpt.c
    syl6breqr
    ralrimiva
    jca
end
