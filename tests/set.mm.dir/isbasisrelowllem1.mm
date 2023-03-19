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
include "simpll2.mm"
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
include "3coml.mm"
include "expcomd.mm"
include "ad2ant2l.mm"
include "jcad.mm"
include "prth.mm"
include "syl6.mm"
include "com23.mm"
include "syl8.mm"
include "imp31.mm"
include "ancrd.mm"
include "an42.mm"
include "syl6ib.mm"
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

theorem isbasisrelowllem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume isbasisrelowl.1: |- I = ( [,) " ( RR X. RR ) )

  disjoint I x
  disjoint I y
  disjoint I z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint a b
  disjoint a x
  disjoint a z
  disjoint b x
  disjoint b z
  disjoint b c
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint c d
  disjoint d y
  disjoint d z
  assert |- ( ( ( ( a e. RR /\ b e. RR /\ x = { z e. RR | ( a <_ z /\ z < b ) } ) /\ ( c e. RR /\ d e. RR /\ y = { z e. RR | ( c <_ z /\ z < d ) } ) ) /\ ( a <_ c /\ b <_ d ) ) -> ( x i^i y ) e. I )

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
    @2
    @14
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
    @17
    @7
    wa
    #
    vz
    cr
    crab
    #
    wceq
    #
    vb
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
    @32
    wa
    #
    vc
    wex
    #
    @33
    @27
    @34
    @35
    @27
    @13
    @32
    @13
    @15
    @21
    @11
    @26
    simplr1
    @27
    @3
    @31
    wa
    #
    vb
    wex
    #
    @32
    @27
    @36
    @37
    @27
    @3
    @31
    @1
    @3
    @10
    @22
    @26
    simpll2
    @27
    vz
    @28
    @30
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
    @29
    vz
    cr
    nfrab1
    @27
    @5
    @28
    wcel
    #
    @5
    cr
    wcel
    #
    @29
    wa
    #
    @5
    @30
    wcel
    @27
    @38
    @40
    @27
    @38
    @39
    @8
    @19
    wa
    #
    wa
    #
    @40
    @23
    @38
    @42
    wb
    #
    @26
    @11
    @10
    @21
    @43
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
    @38
    @39
    @8
    wa
    #
    @39
    @19
    wa
    #
    wa
    #
    @42
    @10
    @38
    @44
    @5
    @16
    wcel
    #
    wa
    #
    @21
    @46
    @38
    @5
    @4
    wcel
    #
    @47
    wa
    @10
    @48
    @5
    @4
    @16
    elin
    @10
    @49
    @44
    @47
    @10
    @49
    @5
    @9
    wcel
    @44
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
    @47
    @45
    @44
    @21
    @47
    @5
    @20
    wcel
    @45
    @16
    @20
    @5
    eleq2
    @19
    vz
    cr
    rabid
    syl6bb
    anbi2d
    sylan9bb
    @46
    @39
    @39
    wa
    #
    @41
    wa
    @42
    @39
    @8
    @39
    @19
    an4
    @50
    @39
    @41
    @39
    anidm
    anbi1i
    bitri
    syl6bb
    syl2an
    adantr
    #
    @42
    @39
    @17
    @7
    @39
    @41
    simpl
    @39
    @8
    @17
    @18
    simprrl
    @39
    @6
    @7
    @19
    simprlr
    jca32
    syl6bi
    @27
    @29
    @39
    @38
    @27
    @29
    @39
    @38
    @27
    @29
    wa
    #
    @39
    wa
    @38
    @42
    @27
    @39
    @29
    @42
    @27
    @39
    wa
    @29
    @42
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
    @39
    @29
    @42
    wi
    @11
    @53
    @22
    @54
    @1
    @3
    @10
    3simpa
    @13
    @15
    @21
    3simpa
    anim12i
    @55
    @26
    wa
    #
    @39
    wa
    #
    @29
    @41
    @39
    @57
    @29
    @6
    @18
    wa
    #
    @29
    wa
    #
    @41
    @57
    @29
    @58
    @55
    @26
    @39
    @29
    @58
    wi
    #
    @55
    @26
    @39
    @17
    @6
    wi
    #
    @7
    @18
    wi
    #
    wa
    #
    @60
    @55
    @39
    @26
    @63
    @55
    @39
    @24
    @61
    wi
    #
    @25
    @62
    wi
    #
    wa
    @26
    @63
    wi
    @55
    @39
    @64
    @65
    @1
    @13
    @39
    @64
    wi
    @3
    @15
    @1
    @13
    wa
    @39
    @24
    @17
    @6
    @1
    @13
    @39
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
    @39
    @65
    wi
    @1
    @13
    @3
    @15
    @39
    @65
    @3
    @15
    @39
    w3a
    @7
    @25
    @18
    @39
    @3
    @15
    @7
    @25
    wa
    @18
    wi
    @5
    @2
    @14
    ltletr
    3coml
    expcomd
    3expia
    ad2ant2l
    jcad
    @24
    @61
    @25
    @62
    prth
    syl6
    com23
    @17
    @6
    @7
    @18
    prth
    syl8
    imp31
    ancrd
    @59
    @6
    @17
    wa
    @7
    @18
    wa
    wa
    @41
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
    syl6ib
    @56
    @39
    simpr
    jctild
    sylanl1
    imp
    an32s
    @52
    @43
    @39
    @27
    @43
    @29
    @51
    adantr
    adantr
    mpbird
    expl
    ancomsd
    impbid
    @29
    vz
    cr
    rabid
    syl6bbr
    eqrd
    jca
    @36
    vb
    19.8a
    syl
    @31
    vb
    cr
    df-rex
    sylibr
    jca
    @34
    vc
    19.8a
    syl
    @32
    vc
    cr
    df-rex
    sylibr
    vz
    cI
    @28
    vc
    vb
    isbasisrelowl.1
    icoreelrnab
    sylibr
end
