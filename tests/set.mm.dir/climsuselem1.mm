include "wcel.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "adantl.mm"
include "simpl.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "imbi2d.mm"
include "cz.mm"
include "syl6eleq.mm"
include "a1i.mm"
include "simpr.mm"
include "simpll.mm"
include "simplr.mm"
include "mpd.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "eluzelz.mm"
include "3ad2ant2.mm"
include "peano2zd.mm"
include "zred.mm"
include "cr.mm"
include "eluzelre.mm"
include "3ad2ant3.mm"
include "1red.mm"
include "readdcld.mm"
include "wss.mm"
include "eqimss2i.mm"
include "sseld.mm"
include "imdistani.mm"
include "syl.mm"
include "3adant3.mm"
include "eluzle.mm"
include "leadd1dd.mm"
include "letrd.mm"
include "wb.mm"
include "eluz.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "syl3anc.mm"
include "exp31.mm"
include "uzind4.mm"
include "sylc.mm"

theorem climsuselem1
  let wph: wff ph
  let vk: setvar k
  let cI: class I
  let cK: class K
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  assume climsuselem1.1: |- Z = ( ZZ>= ` M )
  assume climsuselem1.2: |- ( ph -> M e. ZZ )
  assume climsuselem1.3: |- ( ph -> ( I ` M ) e. Z )
  assume climsuselem1.4: |- ( ( ph /\ k e. Z ) -> ( I ` ( k + 1 ) ) e. ( ZZ>= ` ( ( I ` k ) + 1 ) ) )

  disjoint k ph
  disjoint I k
  disjoint M k
  disjoint Z k
  disjoint j k
  disjoint j ph
  disjoint I j
  disjoint K j
  disjoint M j
  disjoint Z j
  assert |- ( ( ph /\ K e. Z ) -> ( I ` K ) e. ( ZZ>= ` K ) )

  proof
    wph
    cK
    cZ
    wcel
    #
    wa
    cK
    cM
    cuz
    cfv
    #
    wcel
    #
    wph
    cK
    cI
    cfv
    #
    cK
    cuz
    cfv
    #
    wcel
    #
    @0
    @2
    wph
    @0
    @2
    cZ
    @1
    cK
    climsuselem1.1
    eleq2i
    biimpi
    adantl
    wph
    @0
    simpl
    wph
    vj
    cv
    #
    cI
    cfv
    #
    @6
    cuz
    cfv
    #
    wcel
    #
    wi
    wph
    cM
    cI
    cfv
    #
    @1
    wcel
    #
    wi
    #
    wph
    vk
    cv
    #
    cI
    cfv
    #
    @13
    cuz
    cfv
    #
    wcel
    #
    wi
    #
    wph
    @13
    c1
    caddc
    co
    #
    cI
    cfv
    #
    @18
    cuz
    cfv
    #
    wcel
    #
    wi
    wph
    @5
    wi
    vj
    vk
    cM
    cK
    @6
    cM
    wceq
    #
    @9
    @11
    wph
    @22
    @7
    @10
    @8
    @1
    @6
    cM
    cI
    fveq2
    @6
    cM
    cuz
    fveq2
    eleq12d
    imbi2d
    @6
    @13
    wceq
    #
    @9
    @16
    wph
    @23
    @7
    @14
    @8
    @15
    @6
    @13
    cI
    fveq2
    @6
    @13
    cuz
    fveq2
    eleq12d
    imbi2d
    @6
    @18
    wceq
    #
    @9
    @21
    wph
    @24
    @7
    @19
    @8
    @20
    @6
    @18
    cI
    fveq2
    @6
    @18
    cuz
    fveq2
    eleq12d
    imbi2d
    @6
    cK
    wceq
    #
    @9
    @5
    wph
    @25
    @7
    @3
    @8
    @4
    @6
    cK
    cI
    fveq2
    @6
    cK
    cuz
    fveq2
    eleq12d
    imbi2d
    @12
    cM
    cz
    wcel
    wph
    @10
    cZ
    @1
    climsuselem1.3
    climsuselem1.1
    syl6eleq
    a1i
    @13
    @1
    wcel
    #
    @17
    wph
    @21
    @26
    @17
    wa
    #
    wph
    wa
    #
    wph
    @26
    @16
    @21
    @27
    wph
    simpr
    #
    @26
    @17
    wph
    simpll
    @28
    wph
    @16
    @29
    @26
    @17
    wph
    simplr
    mpd
    wph
    @26
    @16
    w3a
    #
    @21
    @18
    @19
    cle
    wbr
    #
    @30
    @18
    @14
    c1
    caddc
    co
    #
    @19
    @30
    @18
    @30
    @13
    @26
    wph
    @13
    cz
    wcel
    @16
    cM
    @13
    eluzelz
    3ad2ant2
    #
    peano2zd
    #
    zred
    @30
    @14
    c1
    @16
    wph
    @14
    cr
    wcel
    @26
    @13
    @14
    eluzelre
    3ad2ant3
    #
    @30
    1red
    #
    readdcld
    @30
    @19
    @30
    @19
    @32
    cuz
    cfv
    wcel
    #
    @19
    cz
    wcel
    #
    wph
    @26
    @37
    @16
    wph
    @26
    wa
    wph
    @13
    cZ
    wcel
    #
    wa
    @37
    wph
    @26
    @39
    wph
    @1
    cZ
    @13
    @1
    cZ
    wss
    wph
    cZ
    @1
    climsuselem1.1
    eqimss2i
    a1i
    sseld
    imdistani
    climsuselem1.4
    syl
    3adant3
    #
    @32
    @19
    eluzelz
    syl
    #
    zred
    @30
    @13
    @14
    c1
    @30
    @13
    @33
    zred
    @35
    @36
    @16
    wph
    @13
    @14
    cle
    wbr
    @26
    @13
    @14
    eluzle
    3ad2ant3
    leadd1dd
    @30
    @37
    @32
    @19
    cle
    wbr
    @40
    @32
    @19
    eluzle
    syl
    letrd
    @30
    @18
    cz
    wcel
    @38
    @21
    @31
    wb
    @34
    @41
    @18
    @19
    eluz
    syl2anc
    mpbird
    syl3anc
    exp31
    uzind4
    sylc
end
