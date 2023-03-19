include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "crab.mm"
include "wceq.mm"
include "w3a.mm"
include "cin.mm"
include "wrex.mm"
include "wex.mm"
include "simplr1.mm"
include "simplr2.mm"
include "nfv.mm"
include "nfrab1.mm"
include "nfeq2.mm"
include "nf3an.mm"
include "nfan.mm"
include "nfcv.mm"
include "wb.mm"
include "simp3.mm"
include "elin.mm"
include "eleq2.mm"
include "rabid.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "anbi2d.mm"
include "sylan9bb.mm"
include "an4.mm"
include "anidm.mm"
include "anbi1i.mm"
include "bitri.mm"
include "an42.mm"
include "bicomi.mm"
include "anbi2i.mm"
include "syl2an.mm"
include "adantr.mm"
include "simpl.mm"
include "simprrl.mm"
include "simprlr.mm"
include "jca32.mm"
include "syl6bi.mm"
include "wi.mm"
include "3simpa.mm"
include "anim12i.mm"
include "letr.mm"
include "3expia.mm"
include "exp4a.mm"
include "ad2ant2r.mm"
include "ltletr.mm"
include "3com13.mm"
include "expcomd.mm"
include "ad2ant2l.mm"
include "jcad.mm"
include "prth.mm"
include "syl6.mm"
include "com23.mm"
include "syl8.mm"
include "imp31.mm"
include "ancrd.mm"
include "syl6ibr.mm"
include "simpr.mm"
include "jctild.mm"
include "sylanl1.mm"
include "imp.mm"
include "an32s.mm"
include "mpbird.mm"
include "expl.mm"
include "ancomsd.mm"
include "impbid.mm"
include "syl6bbr.mm"
include "eqrd.mm"
include "jca.mm"
include "19.8a.mm"
include "syl.mm"
include "df-rex.mm"
include "sylibr.mm"
include "icoreelrnab.mm"

theorem isbasisrelowllem2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume isbasisrelowl.1: |- I = ( [,) " ( RR X. RR ) )

  disjoint a z
  disjoint b z
  disjoint c d
  disjoint c x
  disjoint c z
  disjoint d x
  disjoint d z
  disjoint x z
  disjoint c y
  disjoint d y
  disjoint y z
  assert |- ( ( ( ( a e. RR /\ b e. RR /\ x = { z e. RR | ( a <_ z /\ z < b ) } ) /\ ( c e. RR /\ d e. RR /\ y = { z e. RR | ( c <_ z /\ z < d ) } ) ) /\ ( a <_ c /\ d <_ b ) ) -> ( x i^i y ) e. I )

  proof
    va
    cv
    #
    cr
    wcel
    #
    vb
    cv
    #
    cr
    wcel
    #
    vx
    cv
    #
    @0
    vz
    cv
    #
    cle
    wbr
    #
    @5
    @2
    clt
    wbr
    #
    wa
    #
    vz
    cr
    crab
    #
    wceq
    #
    w3a
    #
    vc
    cv
    #
    cr
    wcel
    #
    vd
    cv
    #
    cr
    wcel
    #
    vy
    cv
    #
    @12
    @5
    cle
    wbr
    #
    @5
    @14
    clt
    wbr
    #
    wa
    #
    vz
    cr
    crab
    #
    wceq
    #
    w3a
    #
    wa
    #
    @0
    @12
    cle
    wbr
    #
    @14
    @2
    cle
    wbr
    #
    wa
    #
    wa
    #
    @4
    @16
    cin
    #
    @20
    wceq
    #
    vd
    cr
    wrex
    #
    vc
    cr
    wrex
    #
    @28
    cI
    wcel
    @27
    @13
    @30
    wa
    #
    vc
    wex
    #
    @31
    @27
    @32
    @33
    @27
    @13
    @30
    @13
    @15
    @21
    @11
    @26
    simplr1
    @27
    @15
    @29
    wa
    #
    vd
    wex
    #
    @30
    @27
    @34
    @35
    @27
    @15
    @29
    @13
    @15
    @21
    @11
    @26
    simplr2
    @27
    vz
    @28
    @20
    @23
    @26
    vz
    @11
    @22
    vz
    @1
    @3
    @10
    vz
    @1
    vz
    nfv
    @3
    vz
    nfv
    vz
    @4
    @9
    @8
    vz
    cr
    nfrab1
    nfeq2
    nf3an
    @13
    @15
    @21
    vz
    @13
    vz
    nfv
    @15
    vz
    nfv
    vz
    @16
    @20
    @19
    vz
    cr
    nfrab1
    #
    nfeq2
    nf3an
    nfan
    @26
    vz
    nfv
    nfan
    vz
    @28
    nfcv
    @36
    @27
    @5
    @28
    wcel
    #
    @5
    cr
    wcel
    #
    @19
    wa
    #
    @5
    @20
    wcel
    #
    @27
    @37
    @39
    @27
    @37
    @38
    @6
    @18
    wa
    #
    @17
    @7
    wa
    #
    wa
    #
    wa
    #
    @39
    @23
    @37
    @44
    wb
    #
    @26
    @11
    @10
    @21
    @45
    @22
    @1
    @3
    @10
    simp3
    @13
    @15
    @21
    simp3
    @10
    @21
    wa
    @37
    @38
    @8
    wa
    #
    @39
    wa
    #
    @44
    @10
    @37
    @46
    @5
    @16
    wcel
    #
    wa
    #
    @21
    @47
    @37
    @5
    @4
    wcel
    #
    @48
    wa
    @10
    @49
    @5
    @4
    @16
    elin
    @10
    @50
    @46
    @48
    @10
    @50
    @5
    @9
    wcel
    @46
    @4
    @9
    @5
    eleq2
    @8
    vz
    cr
    rabid
    syl6bb
    anbi1d
    syl5bb
    @21
    @48
    @39
    @46
    @21
    @48
    @40
    @39
    @16
    @20
    @5
    eleq2
    @19
    vz
    cr
    rabid
    #
    syl6bb
    anbi2d
    sylan9bb
    @47
    @38
    @8
    @19
    wa
    #
    wa
    #
    @44
    @47
    @38
    @38
    wa
    #
    @52
    wa
    @53
    @38
    @8
    @38
    @19
    an4
    @54
    @38
    @52
    @38
    anidm
    anbi1i
    bitri
    @52
    @43
    @38
    @43
    @52
    @43
    @6
    @17
    wa
    #
    @18
    @7
    wa
    wa
    #
    @52
    @6
    @18
    @17
    @7
    an4
    @52
    @56
    @6
    @7
    @17
    @18
    an42
    bicomi
    bitri
    bicomi
    anbi2i
    bitri
    syl6bb
    syl2an
    adantr
    #
    @44
    @38
    @17
    @18
    @38
    @43
    simpl
    @38
    @41
    @17
    @7
    simprrl
    @38
    @6
    @18
    @42
    simprlr
    jca32
    syl6bi
    @27
    @19
    @38
    @37
    @27
    @19
    @38
    @37
    @27
    @19
    wa
    #
    @38
    wa
    @37
    @44
    @27
    @38
    @19
    @44
    @27
    @38
    wa
    @19
    @44
    @23
    @1
    @3
    wa
    #
    @13
    @15
    wa
    #
    wa
    #
    @26
    @38
    @19
    @44
    wi
    @11
    @59
    @22
    @60
    @1
    @3
    @10
    3simpa
    @13
    @15
    @21
    3simpa
    anim12i
    @61
    @26
    wa
    #
    @38
    wa
    #
    @19
    @43
    @38
    @63
    @19
    @52
    @43
    @63
    @19
    @8
    @61
    @26
    @38
    @19
    @8
    wi
    #
    @61
    @26
    @38
    @17
    @6
    wi
    #
    @18
    @7
    wi
    #
    wa
    #
    @64
    @61
    @38
    @26
    @67
    @61
    @38
    @24
    @65
    wi
    #
    @25
    @66
    wi
    #
    wa
    @26
    @67
    wi
    @61
    @38
    @68
    @69
    @1
    @13
    @38
    @68
    wi
    @3
    @15
    @1
    @13
    wa
    @38
    @24
    @17
    @6
    @1
    @13
    @38
    @24
    @17
    wa
    @6
    wi
    @0
    @12
    @5
    letr
    3expia
    exp4a
    ad2ant2r
    @3
    @15
    @38
    @69
    wi
    @1
    @13
    @3
    @15
    @38
    @69
    @3
    @15
    @38
    w3a
    @18
    @25
    @7
    @38
    @15
    @3
    @18
    @25
    wa
    @7
    wi
    @5
    @14
    @2
    ltletr
    3com13
    expcomd
    3expia
    ad2ant2l
    jcad
    @24
    @65
    @25
    @66
    prth
    syl6
    com23
    @17
    @6
    @18
    @7
    prth
    syl8
    imp31
    ancrd
    @43
    @55
    @7
    @18
    wa
    wa
    @52
    @6
    @18
    @17
    @7
    an42
    @6
    @17
    @7
    @18
    an4
    bitri
    syl6ibr
    @62
    @38
    simpr
    jctild
    sylanl1
    imp
    an32s
    @58
    @45
    @38
    @27
    @45
    @19
    @57
    adantr
    adantr
    mpbird
    expl
    ancomsd
    impbid
    @51
    syl6bbr
    eqrd
    jca
    @34
    vd
    19.8a
    syl
    @29
    vd
    cr
    df-rex
    sylibr
    jca
    @32
    vc
    19.8a
    syl
    @30
    vc
    cr
    df-rex
    sylibr
    vz
    cI
    @28
    vc
    vd
    isbasisrelowl.1
    icoreelrnab
    sylibr
end
