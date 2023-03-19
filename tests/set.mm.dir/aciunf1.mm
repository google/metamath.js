include "c0.mm"
include "wne.mm"
include "crab.mm"
include "ciun.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "wf1.mm"
include "cfv.mm"
include "c2nd.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cvv.mm"
include "wss.mm"
include "wcel.mm"
include "ssrab2.mm"
include "ssexg.mm"
include "sylancr.mm"
include "rabid.mm"
include "biimpi.mm"
include "adantl.mm"
include "simprd.mm"
include "nfrab1.mm"
include "simpld.mm"
include "syldan.mm"
include "aciunf1lem.mm"
include "eqidd.mm"
include "cdif.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfdif.mm"
include "wtru.mm"
include "wn.mm"
include "difrab.mm"
include "rabtru.mm"
include "difeq1i.mm"
include "truan.mm"
include "df-ne.mm"
include "bitr4i.mm"
include "rabbii.mm"
include "3eqtr3i.mm"
include "a1i.mm"
include "iuneq12df.mm"
include "ralrimiva.mm"
include "iunxdif3.mm"
include "syl.mm"
include "eqtr3d.mm"
include "xpeq2d.mm"
include "xp0.mm"
include "syl6eq.mm"
include "f1eq123d.mm"
include "raleqdv.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "mpbid.mm"

theorem aciunf1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  let cV: class V
  let cW: class W
  assume aciunf1.0: |- ( ph -> A e. V )
  assume aciunf1.1: |- ( ( ph /\ j e. A ) -> B e. W )

  disjoint A j
  disjoint A k
  disjoint A f
  disjoint j k
  disjoint f j
  disjoint f k
  disjoint B f
  disjoint B k
  disjoint W j
  disjoint f ph
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> E. f ( f : U_ j e. A B -1-1-> U_ j e. A ( { j } X. B ) /\ A. k e. U_ j e. A B ( 2nd ` ( f ` k ) ) = k ) )

  proof
    wph
    vj
    cB
    c0
    wne
    #
    vj
    cA
    crab
    #
    cB
    ciun
    #
    vj
    @1
    vj
    cv
    #
    csn
    #
    cB
    cxp
    #
    ciun
    #
    vf
    cv
    #
    wf1
    #
    vk
    cv
    #
    @7
    cfv
    c2nd
    cfv
    @9
    wceq
    #
    vk
    @2
    wral
    #
    wa
    #
    vf
    wex
    vj
    cA
    cB
    ciun
    #
    vj
    cA
    @5
    ciun
    #
    @7
    wf1
    #
    @10
    vk
    @13
    wral
    #
    wa
    #
    vf
    wex
    wph
    vk
    @1
    cB
    vf
    vj
    cvv
    cW
    wph
    @1
    cA
    wss
    cA
    cV
    wcel
    @1
    cvv
    wcel
    @0
    vj
    cA
    ssrab2
    aciunf1.0
    @1
    cA
    cV
    ssexg
    sylancr
    wph
    @3
    @1
    wcel
    #
    wa
    #
    @3
    cA
    wcel
    #
    @0
    @18
    @20
    @0
    wa
    #
    wph
    @18
    @21
    @0
    vj
    cA
    rabid
    biimpi
    adantl
    #
    simprd
    @0
    vj
    cA
    nfrab1
    #
    wph
    @18
    @20
    cB
    cW
    wcel
    @19
    @20
    @0
    @22
    simpld
    aciunf1.1
    syldan
    aciunf1lem
    wph
    @12
    @17
    vf
    wph
    @8
    @15
    @11
    @16
    wph
    @2
    @13
    @6
    @14
    @7
    @7
    wph
    @7
    eqidd
    wph
    vj
    cA
    cB
    c0
    wceq
    #
    vj
    cA
    crab
    #
    cdif
    #
    cB
    ciun
    #
    @2
    @13
    wph
    vj
    @26
    @1
    cB
    cB
    wph
    vj
    nfv
    #
    vj
    cA
    @25
    vj
    cA
    nfcv
    #
    @24
    vj
    cA
    nfrab1
    #
    nfdif
    #
    @23
    @26
    @1
    wceq
    wph
    wtru
    vj
    cA
    crab
    #
    @25
    cdif
    wtru
    @24
    wn
    #
    wa
    #
    vj
    cA
    crab
    @26
    @1
    wtru
    @24
    vj
    cA
    difrab
    @32
    cA
    @25
    vj
    cA
    @29
    rabtru
    difeq1i
    @34
    @0
    vj
    cA
    @34
    @33
    @0
    @33
    truan
    cB
    c0
    df-ne
    bitr4i
    rabbii
    3eqtr3i
    a1i
    #
    wph
    cB
    eqidd
    iuneq12df
    wph
    @24
    vj
    @25
    wral
    @27
    @13
    wceq
    wph
    @24
    vj
    @25
    wph
    @3
    @25
    wcel
    #
    wa
    #
    @20
    @24
    @36
    @20
    @24
    wa
    #
    wph
    @36
    @38
    @24
    vj
    cA
    rabid
    biimpi
    adantl
    simprd
    #
    ralrimiva
    vj
    cA
    cB
    @25
    @30
    iunxdif3
    syl
    eqtr3d
    #
    wph
    vj
    @26
    @5
    ciun
    #
    @6
    @14
    wph
    vj
    @26
    @1
    @5
    @5
    @28
    @31
    @23
    @35
    wph
    @5
    eqidd
    iuneq12df
    wph
    @5
    c0
    wceq
    #
    vj
    @25
    wral
    @41
    @14
    wceq
    wph
    @42
    vj
    @25
    @37
    @5
    @4
    c0
    cxp
    c0
    @37
    cB
    c0
    @4
    @39
    xpeq2d
    @4
    xp0
    syl6eq
    ralrimiva
    vj
    cA
    @5
    @25
    @30
    iunxdif3
    syl
    eqtr3d
    f1eq123d
    wph
    @10
    vk
    @2
    @13
    @40
    raleqdv
    anbi12d
    exbidv
    mpbid
end
