include "cmeas.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "wn.mm"
include "crab.mm"
include "cdm.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cae.mm"
include "wbr.mm"
include "cun.mm"
include "wo.mm"
include "unrab.mm"
include "ianor.mm"
include "rabbii.mm"
include "eqtr4i.mm"
include "fveq2i.mm"
include "eqeq1i.mm"
include "cle.mm"
include "measbasedom.mm"
include "biimpi.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "simp2.mm"
include "csiga.mm"
include "dmmeas.mm"
include "unelsiga.mm"
include "syl3an1.mm"
include "wss.mm"
include "ssun1.mm"
include "a1i.mm"
include "measssd.mm"
include "simpr.mm"
include "breqtrd.mm"
include "measle0.mm"
include "syl3anc.mm"
include "simp3.mm"
include "ssun2.mm"
include "jca.mm"
include "measbase.mm"
include "syl.mm"
include "cxad.mm"
include "co.mm"
include "measunl.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "cxr.mm"
include "0xr.mm"
include "xaddid1.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "impbida.mm"
include "syl5bbr.mm"
include "wb.mm"
include "braew.mm"
include "anbi12d.mm"
include "3bitr4d.mm"

theorem aean
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cM: class M
  let cO: class O
  assume aean.1: |- U. dom M = O

  disjoint O x
  assert |- ( ( M e. U. ran measures /\ { x e. O | -. ph } e. dom M /\ { x e. O | -. ps } e. dom M ) -> ( { x e. O | ( ph /\ ps ) } ae M <-> ( { x e. O | ph } ae M /\ { x e. O | ps } ae M ) ) )

  proof
    cM
    cmeas
    crn
    cuni
    wcel
    #
    wph
    wn
    #
    vx
    cO
    crab
    #
    cM
    cdm
    #
    wcel
    #
    wps
    wn
    #
    vx
    cO
    crab
    #
    @3
    wcel
    #
    w3a
    #
    wph
    wps
    wa
    #
    wn
    #
    vx
    cO
    crab
    #
    cM
    cfv
    #
    cc0
    wceq
    #
    @2
    cM
    cfv
    #
    cc0
    wceq
    #
    @6
    cM
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    @9
    vx
    cO
    crab
    cM
    cae
    wbr
    #
    wph
    vx
    cO
    crab
    cM
    cae
    wbr
    #
    wps
    vx
    cO
    crab
    cM
    cae
    wbr
    #
    wa
    #
    @13
    @2
    @6
    cun
    #
    cM
    cfv
    #
    cc0
    wceq
    #
    @8
    @18
    @24
    @12
    cc0
    @23
    @11
    cM
    @23
    @1
    @5
    wo
    #
    vx
    cO
    crab
    @11
    @1
    @5
    vx
    cO
    unrab
    @10
    @26
    vx
    cO
    wph
    wps
    ianor
    rabbii
    eqtr4i
    fveq2i
    eqeq1i
    @8
    @25
    @18
    @8
    @25
    wa
    #
    @15
    @17
    @27
    cM
    @3
    cmeas
    cfv
    wcel
    #
    @4
    @14
    cc0
    cle
    wbr
    @15
    @8
    @28
    @25
    @0
    @4
    @28
    @7
    @0
    @28
    cM
    measbasedom
    biimpi
    3ad2ant1
    #
    adantr
    #
    @8
    @4
    @25
    @0
    @4
    @7
    simp2
    #
    adantr
    @27
    @14
    @24
    cc0
    cle
    @8
    @14
    @24
    cle
    wbr
    @25
    @8
    @2
    @23
    @3
    cM
    @29
    @31
    @0
    @3
    csiga
    crn
    cuni
    wcel
    #
    @4
    @7
    @23
    @3
    wcel
    #
    cM
    dmmeas
    @2
    @6
    @3
    unelsiga
    #
    syl3an1
    #
    @2
    @23
    wss
    @8
    @2
    @6
    ssun1
    a1i
    measssd
    adantr
    @8
    @25
    simpr
    #
    breqtrd
    @2
    @3
    cM
    measle0
    syl3anc
    @27
    @28
    @7
    @16
    cc0
    cle
    wbr
    @17
    @30
    @8
    @7
    @25
    @0
    @4
    @7
    simp3
    #
    adantr
    @27
    @16
    @24
    cc0
    cle
    @8
    @16
    @24
    cle
    wbr
    @25
    @8
    @6
    @23
    @3
    cM
    @29
    @37
    @35
    @6
    @23
    wss
    @8
    @6
    @2
    ssun2
    a1i
    measssd
    adantr
    @36
    breqtrd
    @6
    @3
    cM
    measle0
    syl3anc
    jca
    @8
    @18
    wa
    #
    @28
    @33
    @24
    cc0
    cle
    wbr
    @25
    @8
    @28
    @18
    @29
    adantr
    #
    @38
    @32
    @4
    @7
    @33
    @38
    @28
    @32
    @39
    @3
    cM
    measbase
    syl
    @8
    @4
    @18
    @31
    adantr
    #
    @8
    @7
    @18
    @37
    adantr
    #
    @34
    syl3anc
    @38
    @24
    @14
    @16
    cxad
    co
    #
    cc0
    cle
    @38
    @2
    @6
    @3
    cM
    @39
    @40
    @41
    measunl
    @38
    @42
    cc0
    cc0
    cxad
    co
    #
    cc0
    @38
    @14
    cc0
    @16
    cc0
    cxad
    @8
    @15
    @17
    simprl
    @8
    @15
    @17
    simprr
    oveq12d
    cc0
    cxr
    wcel
    @43
    cc0
    wceq
    0xr
    cc0
    xaddid1
    ax-mp
    syl6eq
    breqtrd
    @23
    @3
    cM
    measle0
    syl3anc
    impbida
    syl5bbr
    @0
    @4
    @19
    @13
    wb
    @7
    @9
    vx
    cM
    cO
    aean.1
    braew
    3ad2ant1
    @0
    @4
    @22
    @18
    wb
    @7
    @0
    @20
    @15
    @21
    @17
    wph
    vx
    cM
    cO
    aean.1
    braew
    wps
    vx
    cM
    cO
    aean.1
    braew
    anbi12d
    3ad2ant1
    3bitr4d
end
