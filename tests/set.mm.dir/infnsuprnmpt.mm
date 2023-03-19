include "cmpt.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cv.mm"
include "cneg.mm"
include "wcel.mm"
include "crab.mm"
include "csup.mm"
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
include "rnmptlb.mm"
include "infrenegsup.mm"
include "syl3anc.mm"
include "wb.mm"
include "wal.mm"
include "wa.mm"
include "rabidim2.mm"
include "adantl.mm"
include "cvv.mm"
include "negex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "sylib.mm"
include "nfcv.mm"
include "nfneg.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel.mm"
include "nfrab.mm"
include "nfan.mm"
include "wi.mm"
include "rabidim1.mm"
include "w3a.mm"
include "negeq.mm"
include "eqcomd.mm"
include "3ad2ant3.mm"
include "simp1r.mm"
include "recn.mm"
include "negnegd.mm"
include "syl.mm"
include "eqtr2d.mm"
include "3exp.mm"
include "syldan.mm"
include "reximdai.mm"
include "mpd.mm"
include "simpr.mm"
include "elrnmptd.mm"
include "ex.mm"
include "vex.mm"
include "biimpi.mm"
include "simp3.mm"
include "renegcld.mm"
include "3adant3.mm"
include "eqeltrd.mm"
include "simp2.mm"
include "negeqd.mm"
include "recnd.mm"
include "eqtrd.mm"
include "rspe.mm"
include "syl2anc.mm"
include "a1i.mm"
include "jca.mm"
include "rexlimd.mm"
include "imp.mm"
include "rabid.mm"
include "sylibr.mm"
include "impbid.mm"
include "alrimiv.mm"
include "nfrab1.mm"
include "dfcleqf.mm"
include "supeq1d.mm"
include "eqidd.mm"
include "3eqtrd.mm"

theorem infnsuprnmpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  assume infnsuprnmpt.x: |- F/ x ph
  assume infnsuprnmpt.a: |- ( ph -> A =/= (/) )
  assume infnsuprnmpt.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume infnsuprnmpt.l: |- ( ph -> E. y e. RR A. x e. A y <_ B )

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
  disjoint ph z
  assert |- ( ph -> inf ( ran ( x e. A |-> B ) , RR , < ) = -u sup ( ran ( x e. A |-> -u B ) , RR , < ) )

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
    cinf
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
    csup
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
    csup
    #
    cneg
    #
    @13
    wph
    @1
    cr
    wss
    @1
    c0
    wne
    vy
    cv
    vz
    cv
    cle
    wbr
    vz
    @1
    wral
    vy
    cr
    wrex
    @2
    @8
    wceq
    wph
    vx
    cA
    cB
    cr
    @0
    infnsuprnmpt.x
    @0
    eqid
    #
    infnsuprnmpt.b
    rnmptssd
    wph
    vx
    cA
    cB
    @0
    cr
    infnsuprnmpt.x
    infnsuprnmpt.b
    @14
    infnsuprnmpt.a
    rnmptn0
    wph
    vx
    vy
    vz
    cA
    cB
    infnsuprnmpt.l
    rnmptlb
    vy
    vz
    vw
    @1
    infrenegsup
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
    @3
    @6
    wcel
    #
    @3
    @11
    wcel
    #
    wb
    #
    vw
    wal
    @6
    @11
    wceq
    wph
    @17
    vw
    wph
    @15
    @16
    wph
    @15
    @16
    wph
    @15
    wa
    #
    vx
    cA
    @9
    @3
    @10
    @6
    @10
    eqid
    #
    @18
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
    @21
    @15
    @5
    wph
    @5
    vw
    cr
    rabidim2
    adantl
    @4
    cvv
    wcel
    #
    @5
    @21
    wb
    @3
    negex
    #
    vx
    cA
    cB
    @4
    @0
    cvv
    @14
    elrnmpt
    ax-mp
    sylib
    @18
    @20
    @22
    vx
    cA
    wph
    @15
    vx
    infnsuprnmpt.x
    vx
    @3
    @6
    vx
    @3
    nfcv
    #
    @5
    vx
    vw
    cr
    vx
    @4
    @1
    vx
    @3
    @26
    nfneg
    vx
    @0
    vx
    cA
    cB
    nfmpt1
    nfrn
    nfel
    #
    vx
    cr
    nfcv
    #
    nfrab
    nfel
    nfan
    wph
    @15
    @3
    cr
    wcel
    #
    vx
    cv
    cA
    wcel
    #
    @20
    @22
    wi
    wi
    @15
    @29
    wph
    @5
    vw
    cr
    rabidim1
    adantl
    wph
    @29
    wa
    #
    @30
    @20
    @22
    @31
    @30
    @20
    w3a
    #
    @9
    @4
    cneg
    #
    @3
    @20
    @31
    @9
    @33
    wceq
    @30
    @20
    @33
    @9
    @4
    cB
    negeq
    eqcomd
    3ad2ant3
    @32
    @29
    @33
    @3
    wceq
    wph
    @29
    @30
    @20
    simp1r
    @29
    @3
    @3
    recn
    negnegd
    syl
    eqtr2d
    3exp
    syldan
    reximdai
    mpd
    wph
    @15
    simpr
    elrnmptd
    ex
    wph
    @16
    @15
    wph
    @16
    wa
    @29
    @5
    wa
    #
    @15
    wph
    @16
    @23
    @34
    @16
    @23
    wph
    @16
    @23
    @3
    cvv
    wcel
    @16
    @23
    wb
    vw
    vex
    vx
    cA
    @9
    @3
    @10
    cvv
    @19
    elrnmpt
    ax-mp
    biimpi
    adantl
    wph
    @23
    @34
    wph
    @22
    @34
    vx
    cA
    infnsuprnmpt.x
    @29
    @5
    vx
    vx
    @3
    cr
    @26
    @28
    nfel
    @27
    nfan
    wph
    @30
    @22
    @34
    wph
    @30
    @22
    w3a
    #
    @29
    @5
    @35
    @3
    @9
    cr
    wph
    @30
    @22
    simp3
    #
    wph
    @30
    @9
    cr
    wcel
    @22
    wph
    @30
    wa
    #
    cB
    infnsuprnmpt.b
    renegcld
    3adant3
    eqeltrd
    @35
    vx
    cA
    cB
    @4
    @0
    cvv
    @14
    @35
    @30
    @20
    @21
    wph
    @30
    @22
    simp2
    @35
    @4
    @9
    cneg
    #
    cB
    @35
    @3
    @9
    @36
    negeqd
    wph
    @30
    @38
    cB
    wceq
    @22
    @37
    cB
    @37
    cB
    infnsuprnmpt.b
    recnd
    negnegd
    3adant3
    eqtrd
    @20
    vx
    cA
    rspe
    syl2anc
    @24
    @35
    @25
    a1i
    elrnmptd
    jca
    3exp
    rexlimd
    imp
    syldan
    @5
    vw
    cr
    rabid
    sylibr
    ex
    impbid
    alrimiv
    vw
    @6
    @11
    @5
    vw
    cr
    nfrab1
    vw
    @11
    nfcv
    dfcleqf
    sylibr
    supeq1d
    negeqd
    wph
    @13
    eqidd
    3eqtrd
end
