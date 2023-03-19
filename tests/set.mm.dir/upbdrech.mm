include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "ralrimiva.mm"
include "nfra1.mm"
include "nfv.mm"
include "w3a.mm"
include "simp3.mm"
include "rspa.mm"
include "3adant3.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "rexlimd.mm"
include "abssdv.mm"
include "syl.mm"
include "wex.mm"
include "eqidd.mm"
include "rgen.mm"
include "r19.2z.mm"
include "sylancl.mm"
include "nfre1.mm"
include "nfex.mm"
include "wa.mm"
include "simpr.mm"
include "cvv.mm"
include "elex.mm"
include "isset.mm"
include "sylib.mm"
include "rspe.mm"
include "syl2anc.mm"
include "rexcom4.mm"
include "mpd.mm"
include "abn0.mm"
include "sylibr.mm"
include "vex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "biimpi.mm"
include "adantl.mm"
include "nfan.mm"
include "nfsab.mm"
include "wi.mm"
include "simp1r.mm"
include "simp2.mm"
include "eqbrtrd.mm"
include "adantr.mm"
include "3adant2.mm"
include "reximdvai.mm"
include "suprcl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "elabrexg.mm"
include "suprub.mm"
include "syl31anc.mm"
include "syl6breqr.mm"
include "jca.mm"

theorem upbdrech
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  assume upbdrech.a: |- ( ph -> A =/= (/) )
  assume upbdrech.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume upbdrech.bd: |- ( ph -> E. y e. RR A. x e. A B <_ y )
  assume upbdrech.c: |- C = sup ( { z | E. x e. A z = B } , RR , < )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint ph x
  disjoint ph y
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint ph w
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
    vz
    cv
    #
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    vz
    cab
    #
    cr
    clt
    csup
    #
    cr
    upbdrech.c
    wph
    @4
    cr
    wss
    #
    @4
    c0
    wne
    #
    vw
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vw
    @4
    wral
    #
    vy
    cr
    wrex
    #
    @5
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
    #
    @6
    wph
    @13
    vx
    cA
    upbdrech.b
    ralrimiva
    @14
    @3
    vz
    cr
    @14
    @2
    @1
    cr
    wcel
    #
    vx
    cA
    @13
    vx
    cA
    nfra1
    @15
    vx
    nfv
    @14
    vx
    cv
    cA
    wcel
    #
    @2
    @15
    @14
    @16
    @2
    w3a
    @1
    cB
    cr
    @14
    @16
    @2
    simp3
    @14
    @16
    @13
    @2
    @13
    vx
    cA
    rspa
    3adant3
    eqeltrd
    3exp
    rexlimd
    abssdv
    syl
    #
    wph
    @3
    vz
    wex
    #
    @7
    wph
    cB
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @18
    wph
    cA
    c0
    wne
    @19
    vx
    cA
    wral
    @20
    upbdrech.a
    @19
    vx
    cA
    @16
    cB
    eqidd
    rgen
    @19
    vx
    cA
    r19.2z
    sylancl
    wph
    @19
    @18
    vx
    cA
    wph
    vx
    nfv
    #
    @3
    vx
    vz
    @2
    vx
    cA
    nfre1
    #
    nfex
    wph
    @16
    @19
    @18
    wph
    @16
    @18
    @19
    wph
    @16
    wa
    #
    @2
    vz
    wex
    #
    vx
    cA
    wrex
    #
    @18
    @23
    @16
    @24
    @25
    wph
    @16
    simpr
    #
    @23
    cB
    cvv
    wcel
    #
    @24
    @23
    @13
    @27
    upbdrech.b
    cB
    cr
    elex
    syl
    vz
    cB
    isset
    sylib
    @24
    vx
    cA
    rspe
    syl2anc
    @2
    vx
    vz
    cA
    rexcom4
    sylib
    #
    3adant3
    3exp
    rexlimd
    mpd
    @3
    vz
    abn0
    #
    sylibr
    wph
    cB
    @9
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
    @12
    upbdrech.bd
    wph
    @31
    @11
    vy
    cr
    wph
    @9
    cr
    wcel
    #
    @31
    @11
    wph
    @31
    @11
    @32
    wph
    @31
    wa
    #
    @10
    vw
    @4
    @33
    @8
    @4
    wcel
    #
    wa
    #
    @8
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @10
    @34
    @37
    @33
    @34
    @37
    @3
    @37
    vz
    @8
    vw
    vex
    @1
    @8
    wceq
    @2
    @36
    vx
    cA
    @1
    @8
    cB
    eqeq1
    rexbidv
    elab
    biimpi
    adantl
    @35
    @36
    @10
    vx
    cA
    @33
    @34
    vx
    wph
    @31
    vx
    @21
    @30
    vx
    cA
    nfra1
    nfan
    @3
    vx
    vz
    vw
    @22
    nfsab
    nfan
    @10
    vx
    nfv
    @33
    @16
    @36
    @10
    wi
    wi
    @34
    @33
    @16
    @36
    @10
    @33
    @16
    @36
    w3a
    #
    @8
    cB
    @9
    cle
    @33
    @16
    @36
    simp3
    @38
    @31
    @16
    @30
    wph
    @31
    @16
    @36
    simp1r
    @33
    @16
    @36
    simp2
    @30
    vx
    cA
    rspa
    syl2anc
    eqbrtrd
    3exp
    adantr
    rexlimd
    mpd
    ralrimiva
    3adant2
    3exp
    reximdvai
    mpd
    #
    vy
    vw
    @4
    suprcl
    syl3anc
    syl5eqel
    wph
    @0
    vx
    cA
    @23
    cB
    @5
    cC
    cle
    @23
    @6
    @7
    @12
    cB
    @4
    wcel
    #
    cB
    @5
    cle
    wbr
    wph
    @6
    @16
    @17
    adantr
    @23
    @18
    @7
    @28
    @29
    sylibr
    wph
    @12
    @16
    @39
    adantr
    @23
    @16
    @13
    @40
    @26
    upbdrech.b
    vx
    vz
    cA
    cB
    cr
    elabrexg
    syl2anc
    vy
    vw
    @4
    cB
    suprub
    syl31anc
    upbdrech.c
    syl6breqr
    ralrimiva
    jca
end
