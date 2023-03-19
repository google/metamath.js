include "cz.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wral.mm"
include "wss.mm"
include "zre.mm"
include "leidd.mm"
include "jca.mm"
include "ancli.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi12d.mm"
include "elrab.mm"
include "sylibr.mm"
include "wi.mm"
include "peano2z.mm"
include "a1i.mm"
include "adantrd.mm"
include "cr.mm"
include "clt.mm"
include "ltp1.mm"
include "adantl.mm"
include "peano2re.mm"
include "lelttr.mm"
include "3expb.mm"
include "sylan2.mm"
include "mpan2d.mm"
include "ltle.mm"
include "syld.mm"
include "syl2an.mm"
include "expimpd.mm"
include "3exp.mm"
include "imp4d.mm"
include "jcad.mm"
include "3imtr4g.mm"
include "ralrimiv.mm"
include "peano5uzti.mm"
include "mp2and.mm"
include "sseld.mm"
include "3imtr3g.mm"
include "3impib.mm"
include "simprrd.mm"

theorem uzind
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  let vw: setvar w
  assume uzind.1: |- ( j = M -> ( ph <-> ps ) )
  assume uzind.2: |- ( j = k -> ( ph <-> ch ) )
  assume uzind.3: |- ( j = ( k + 1 ) -> ( ph <-> th ) )
  assume uzind.4: |- ( j = N -> ( ph <-> ta ) )
  assume uzind.5: |- ( M e. ZZ -> ps )
  assume uzind.6: |- ( ( M e. ZZ /\ k e. ZZ /\ M <_ k ) -> ( ch -> th ) )

  disjoint N j
  disjoint j ps
  disjoint ch j
  disjoint j th
  disjoint j ta
  disjoint k ph
  disjoint j k
  disjoint M j
  disjoint M k
  disjoint j w
  disjoint N w
  disjoint k w
  disjoint ph w
  disjoint M w
  assert |- ( ( M e. ZZ /\ N e. ZZ /\ M <_ N ) -> ta )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cN
    cle
    wbr
    #
    w3a
    @1
    @2
    wta
    @0
    @1
    @2
    @1
    @2
    wta
    wa
    #
    wa
    #
    @0
    cN
    cM
    vw
    cv
    #
    cle
    wbr
    #
    vw
    cz
    crab
    #
    wcel
    cN
    cM
    vj
    cv
    #
    cle
    wbr
    #
    wph
    wa
    #
    vj
    cz
    crab
    #
    wcel
    @1
    @2
    wa
    @4
    @0
    @7
    @11
    cN
    @0
    cM
    @11
    wcel
    #
    vk
    cv
    #
    c1
    caddc
    co
    #
    @11
    wcel
    #
    vk
    @11
    wral
    @7
    @11
    wss
    @0
    @0
    cM
    cM
    cle
    wbr
    #
    wps
    wa
    #
    wa
    @12
    @0
    @17
    @0
    @16
    wps
    @0
    cM
    cM
    zre
    #
    leidd
    uzind.5
    jca
    ancli
    @10
    @17
    vj
    cM
    cz
    @8
    cM
    wceq
    @9
    @16
    wph
    wps
    @8
    cM
    cM
    cle
    breq2
    uzind.1
    anbi12d
    elrab
    sylibr
    @0
    @15
    vk
    @11
    @0
    @13
    cz
    wcel
    #
    cM
    @13
    cle
    wbr
    #
    wch
    wa
    #
    wa
    #
    @14
    cz
    wcel
    #
    cM
    @14
    cle
    wbr
    #
    wth
    wa
    #
    wa
    @13
    @11
    wcel
    @15
    @0
    @22
    @23
    @25
    @0
    @19
    @23
    @21
    @19
    @23
    wi
    @0
    @13
    peano2z
    a1i
    adantrd
    @0
    @22
    @24
    wth
    @0
    @19
    @21
    @24
    @0
    @19
    wa
    @20
    @24
    wch
    @0
    cM
    cr
    wcel
    #
    @13
    cr
    wcel
    #
    @20
    @24
    wi
    @19
    @18
    @13
    zre
    @26
    @27
    wa
    #
    @20
    cM
    @14
    clt
    wbr
    #
    @24
    @28
    @20
    @13
    @14
    clt
    wbr
    #
    @29
    @27
    @30
    @26
    @13
    ltp1
    adantl
    @27
    @26
    @27
    @14
    cr
    wcel
    #
    wa
    @20
    @30
    wa
    @29
    wi
    #
    @27
    @31
    @13
    peano2re
    #
    ancli
    @26
    @27
    @31
    @32
    cM
    @13
    @14
    lelttr
    3expb
    sylan2
    mpan2d
    @27
    @26
    @31
    @29
    @24
    wi
    @33
    cM
    @14
    ltle
    sylan2
    syld
    syl2an
    adantrd
    expimpd
    @0
    @19
    @20
    wch
    wth
    @0
    @19
    @20
    wch
    wth
    wi
    uzind.6
    3exp
    imp4d
    jcad
    jcad
    @10
    @21
    vj
    @13
    cz
    @8
    @13
    wceq
    @9
    @20
    wph
    wch
    @8
    @13
    cM
    cle
    breq2
    uzind.2
    anbi12d
    elrab
    @10
    @25
    vj
    @14
    cz
    @8
    @14
    wceq
    @9
    @24
    wph
    wth
    @8
    @14
    cM
    cle
    breq2
    uzind.3
    anbi12d
    elrab
    3imtr4g
    ralrimiv
    vk
    @11
    vw
    cM
    peano5uzti
    mp2and
    sseld
    @6
    @2
    vw
    cN
    cz
    @5
    cN
    cM
    cle
    breq2
    elrab
    @10
    @3
    vj
    cN
    cz
    @8
    cN
    wceq
    @9
    @2
    wph
    wta
    @8
    cN
    cM
    cle
    breq2
    uzind.4
    anbi12d
    elrab
    3imtr3g
    3impib
    simprrd
end
