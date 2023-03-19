include "cres.mm"
include "wf1o.mm"
include "cmpt.mm"
include "crn.mm"
include "wf1.mm"
include "eqid.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "id.mm"
include "sseldi.mm"
include "adantl.mm"
include "syl2anc.mm"
include "syl6eleq.mm"
include "wb.mm"
include "rabid.mm"
include "a1i.mm"
include "mpbid.mm"
include "simprd.mm"
include "wss.mm"
include "wdisj.mm"
include "disjss1.mm"
include "sylc.mm"
include "disjf1.mm"
include "f1f1orn.mm"
include "syl.mm"
include "wceq.mm"
include "reseq1d.mm"
include "resmptd.mm"
include "eqtrd.mm"
include "eqidd.mm"
include "wral.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsni.mm"
include "eldifi.mm"
include "elrnmpt.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel.mm"
include "w3a.mm"
include "simp3.mm"
include "cvv.mm"
include "simp2.mm"
include "eqcomd.mm"
include "eqnetrd.mm"
include "3adant2.mm"
include "jca.mm"
include "sylibr.mm"
include "eqcomi.mm"
include "eleqtrd.mm"
include "eqvisset.mm"
include "3ad2ant3.mm"
include "elrnmpt1.mm"
include "eqeltrd.mm"
include "3adant1l.mm"
include "3exp.mm"
include "rexlimd.mm"
include "imp.mm"
include "syl21anc.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "vex.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "simpr.mm"
include "adantr.mm"
include "3adant1.mm"
include "wn.mm"
include "nelsn.mm"
include "eldifd.mm"
include "syl6eleqr.mm"
include "eqssd.mm"
include "f1oeq123d.mm"
include "mpbird.mm"

theorem disjf1o
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  let vy: setvar y
  assume disjf1o.xph: |- F/ x ph
  assume disjf1o.f: |- F = ( x e. A |-> B )
  assume disjf1o.b: |- ( ( ph /\ x e. A ) -> B e. V )
  assume disjf1o.dj: |- ( ph -> Disj_ x e. A B )
  assume disjf1o.d: |- C = { x e. A | B =/= (/) }
  assume disjf1o.e: |- D = ( ran F \ { (/) } )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint V x
  disjoint B y
  disjoint C y
  disjoint x y
  disjoint D y
  disjoint ph y
  assert |- ( ph -> ( F |` C ) : C -1-1-onto-> D )

  proof
    wph
    cC
    cD
    cF
    cC
    cres
    #
    wf1o
    cC
    vx
    cC
    cB
    cmpt
    #
    crn
    #
    @1
    wf1o
    #
    wph
    cC
    cV
    @1
    wf1
    @3
    wph
    vx
    cC
    cB
    @1
    cV
    disjf1o.xph
    @1
    eqid
    #
    wph
    vx
    cv
    #
    cC
    wcel
    #
    wa
    wph
    @5
    cA
    wcel
    #
    cB
    cV
    wcel
    wph
    @6
    simpl
    @6
    @7
    wph
    @6
    cC
    cA
    @5
    cC
    cB
    c0
    wne
    #
    vx
    cA
    crab
    #
    cA
    disjf1o.d
    @8
    vx
    cA
    ssrab2
    eqsstri
    #
    @6
    id
    #
    sseldi
    #
    adantl
    disjf1o.b
    syl2anc
    @6
    @8
    wph
    @6
    @7
    @8
    @6
    @5
    @9
    wcel
    #
    @7
    @8
    wa
    #
    @6
    @5
    cC
    @9
    @11
    disjf1o.d
    syl6eleq
    @13
    @14
    wb
    @6
    @8
    vx
    cA
    rabid
    #
    a1i
    mpbid
    simprd
    #
    adantl
    wph
    cC
    cA
    wss
    #
    vx
    cA
    cB
    wdisj
    vx
    cC
    cB
    wdisj
    @17
    wph
    @10
    a1i
    #
    disjf1o.dj
    vx
    cC
    cA
    cB
    disjss1
    sylc
    disjf1
    cC
    cV
    @1
    f1f1orn
    syl
    wph
    cC
    cC
    cD
    @2
    @0
    @1
    wph
    @0
    vx
    cA
    cB
    cmpt
    #
    cC
    cres
    @1
    wph
    cF
    @19
    cC
    cF
    @19
    wceq
    wph
    disjf1o.f
    a1i
    reseq1d
    wph
    vx
    cA
    cC
    cB
    @18
    resmptd
    eqtrd
    wph
    cC
    eqidd
    wph
    cD
    @2
    wph
    vy
    cv
    #
    @2
    wcel
    #
    vy
    cD
    wral
    cD
    @2
    wss
    wph
    @21
    vy
    cD
    wph
    @20
    cD
    wcel
    #
    wa
    wph
    @20
    c0
    wne
    #
    @20
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @21
    wph
    @22
    simpl
    @22
    @23
    wph
    @22
    @20
    cF
    crn
    #
    c0
    csn
    #
    cdif
    #
    wcel
    #
    @23
    @22
    @20
    cD
    @28
    @22
    id
    disjf1o.e
    syl6eleq
    #
    @20
    @26
    c0
    eldifsni
    syl
    adantl
    @22
    @25
    wph
    @22
    @20
    @26
    wcel
    #
    @25
    @22
    @29
    @31
    @30
    @20
    @26
    @27
    eldifi
    syl
    #
    @22
    @31
    @31
    @25
    wb
    @32
    vx
    cA
    cB
    @20
    cF
    @26
    disjf1o.f
    elrnmpt
    syl
    mpbid
    adantl
    wph
    @23
    wa
    #
    @25
    @21
    @33
    @24
    @21
    vx
    cA
    wph
    @23
    vx
    disjf1o.xph
    @23
    vx
    nfv
    nfan
    vx
    @20
    @2
    vx
    @20
    nfcv
    vx
    @1
    vx
    cC
    cB
    nfmpt1
    nfrn
    nfel
    @33
    @7
    @24
    @21
    @23
    @7
    @24
    @21
    wph
    @23
    @7
    @24
    w3a
    #
    @20
    cB
    @2
    @23
    @7
    @24
    simp3
    @34
    @6
    cB
    cvv
    wcel
    #
    cB
    @2
    wcel
    @34
    @5
    @9
    cC
    @34
    @14
    @13
    @34
    @7
    @8
    @23
    @7
    @24
    simp2
    @23
    @24
    @8
    @7
    @23
    @24
    wa
    cB
    @20
    c0
    @24
    cB
    @20
    wceq
    @23
    @24
    @20
    cB
    @24
    id
    eqcomd
    adantl
    @23
    @24
    simpl
    eqnetrd
    3adant2
    jca
    @15
    sylibr
    @9
    cC
    wceq
    @34
    cC
    @9
    disjf1o.d
    eqcomi
    a1i
    eleqtrd
    @24
    @23
    @35
    @7
    vy
    cB
    eqvisset
    #
    3ad2ant3
    vx
    cC
    cB
    @1
    cvv
    @4
    elrnmpt1
    syl2anc
    eqeltrd
    3adant1l
    3exp
    rexlimd
    imp
    syl21anc
    ralrimiva
    vy
    cD
    @2
    dfss3
    sylibr
    wph
    @22
    vy
    @2
    wral
    @2
    cD
    wss
    wph
    @22
    vy
    @2
    wph
    @21
    wa
    wph
    @24
    vx
    cC
    wrex
    #
    @22
    wph
    @21
    simpl
    @21
    @37
    wph
    @21
    @37
    @20
    cvv
    wcel
    @21
    @37
    wb
    vy
    vex
    vx
    cC
    cB
    @20
    @1
    cvv
    @4
    elrnmpt
    ax-mp
    biimpi
    adantl
    wph
    @37
    @22
    wph
    @24
    @22
    vx
    cC
    disjf1o.xph
    @22
    vx
    nfv
    wph
    @6
    @24
    @22
    wph
    @6
    @24
    w3a
    #
    @20
    @28
    cD
    @38
    @20
    @26
    @27
    @6
    @24
    @31
    wph
    @6
    @24
    wa
    #
    @20
    cB
    @26
    @6
    @24
    simpr
    #
    @39
    @7
    @35
    cB
    @26
    wcel
    @6
    @7
    @24
    @12
    adantr
    @39
    @24
    @35
    @40
    @36
    syl
    vx
    cA
    cB
    cF
    cvv
    disjf1o.f
    elrnmpt1
    syl2anc
    eqeltrd
    3adant1
    @6
    @24
    @20
    @27
    wcel
    wn
    #
    wph
    @39
    @23
    @41
    @39
    @20
    cB
    c0
    @40
    @6
    @8
    @24
    @16
    adantr
    eqnetrd
    @20
    c0
    nelsn
    syl
    3adant1
    eldifd
    disjf1o.e
    syl6eleqr
    3exp
    rexlimd
    imp
    syl2anc
    ralrimiva
    vy
    @2
    cD
    dfss3
    sylibr
    eqssd
    f1oeq123d
    mpbird
end
