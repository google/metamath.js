include "cv.mm"
include "cat.mm"
include "wcel.mm"
include "wa.mm"
include "cch.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "wn.mm"
include "cin.mm"
include "wi.mm"
include "w3a.mm"
include "c0h.mm"
include "wb.mm"
include "wne.mm"
include "df-ne.mm"
include "atnemeq0.mm"
include "syl5bbr.mm"
include "anbi2d.mm"
include "3adant3.mm"
include "atelch.mm"
include "atexch.mm"
include "syl3an1.mm"
include "sylbid.mm"
include "expd.mm"
include "3com23.mm"
include "3expa.mm"
include "adantrl.mm"
include "adantrd.mm"
include "imp32.mm"
include "adantrr.mm"
include "simplrl.mm"
include "anim1i.mm"
include "ancoms.mm"
include "chub2.mm"
include "mpan.mm"
include "sstr.mm"
include "sylan2.mm"
include "chub1.mm"
include "mpan2.mm"
include "anim12i.mm"
include "anandirs.mm"
include "adantll.mm"
include "chjcl.mm"
include "chlub.mm"
include "syl3an3.mm"
include "adantr.mm"
include "mpbid.mm"
include "chlejb2.mm"
include "biimpa.mm"
include "ad2ant2lr.mm"
include "sseqtrd.mm"
include "exp45.mm"
include "anasss.mm"
include "syl2an.mm"
include "adantlr.mm"
include "syl7.mm"
include "imp44.mm"
include "sstrd.mm"
include "simplrr.mm"
include "ad2antlr.mm"
include "adantl.mm"
include "ssind.mm"
include "chincl.mm"
include "chlej1.mm"
include "ex.mm"
include "syl3an2.mm"
include "3comr.mm"
include "chlej2.mm"
include "mp3anl2.mm"
include "sylanl2.mm"
include "adantllr.mm"
include "sstr2.mm"
include "syl5com.mm"
include "chjcom.mm"
include "ad2antrr.mm"
include "sseq1d.mm"
include "sylibrd.mm"
include "syld.mm"
include "ad2antrl.mm"
include "exp32.mm"
include "sylan.mm"
include "imp31.mm"
include "mpd.mm"
include "exp4d.mm"
include "com34.mm"
include "imp4c.mm"
include "com24.mm"

theorem mdsymlem5
  let cA: class A
  let cB: class B
  let cC: class C
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vc: setvar c
  assume mdsymlem1.1: |- A e. CH
  assume mdsymlem1.2: |- B e. CH
  assume mdsymlem1.3: |- C = ( A vH p )

  disjoint q r
  disjoint C q
  disjoint C r
  disjoint c p
  disjoint c q
  disjoint c r
  disjoint A c
  disjoint p q
  disjoint p r
  disjoint A p
  disjoint A q
  disjoint A r
  disjoint B c
  disjoint B p
  disjoint B q
  disjoint B r
  assert |- ( ( q e. HAtoms /\ r e. HAtoms ) -> ( -. q = p -> ( ( p C_ ( q vH r ) /\ ( q C_ A /\ r C_ B ) ) -> ( ( ( c e. CH /\ A C_ c ) /\ p e. HAtoms ) -> ( p C_ c -> p C_ ( ( c i^i B ) vH A ) ) ) ) ) )

  proof
    vq
    cv
    #
    cat
    wcel
    #
    vr
    cv
    #
    cat
    wcel
    #
    wa
    #
    vc
    cv
    #
    cch
    wcel
    #
    cA
    @5
    wss
    #
    wa
    vp
    cv
    #
    cat
    wcel
    #
    wa
    @8
    @0
    @2
    chj
    co
    #
    wss
    #
    @0
    cA
    wss
    #
    @2
    cB
    wss
    #
    wa
    #
    wa
    #
    @0
    @8
    wceq
    wn
    #
    @8
    @5
    wss
    #
    @8
    @5
    cB
    cin
    #
    cA
    chj
    co
    #
    wss
    #
    wi
    #
    @4
    @6
    @7
    @9
    @15
    @16
    @21
    wi
    wi
    #
    @4
    @6
    @9
    @7
    @22
    @4
    @6
    @9
    @7
    @22
    wi
    @4
    @6
    @9
    wa
    #
    wa
    #
    @7
    @15
    @16
    @21
    @24
    @7
    @15
    @16
    wa
    #
    wa
    #
    @17
    @20
    @24
    @26
    @17
    wa
    #
    wa
    #
    @2
    @18
    wss
    #
    @20
    @28
    @2
    @5
    cB
    @28
    @2
    @0
    @8
    chj
    co
    #
    @5
    @24
    @26
    @2
    @30
    wss
    #
    @17
    @24
    @25
    @31
    @7
    @24
    @15
    @16
    @31
    @24
    @11
    @16
    @31
    wi
    #
    @14
    @4
    @9
    @11
    @32
    wi
    #
    @6
    @1
    @3
    @9
    @33
    @1
    @9
    @3
    @33
    @1
    @9
    @3
    w3a
    #
    @11
    @16
    @31
    @34
    @11
    @16
    wa
    #
    @11
    @0
    @8
    cin
    c0h
    wceq
    #
    wa
    #
    @31
    @1
    @9
    @35
    @37
    wb
    @3
    @1
    @9
    wa
    #
    @16
    @36
    @11
    @16
    @0
    @8
    wne
    @38
    @36
    @0
    @8
    df-ne
    @0
    @8
    atnemeq0
    syl5bbr
    anbi2d
    3adant3
    @1
    @0
    cch
    wcel
    #
    @9
    @3
    @37
    @31
    wi
    @0
    atelch
    #
    @0
    @8
    @2
    atexch
    syl3an1
    sylbid
    expd
    3com23
    3expa
    adantrl
    adantrd
    imp32
    adantrl
    adantrr
    @24
    @7
    @25
    @17
    @30
    @5
    wss
    #
    @25
    @12
    @24
    @7
    @17
    @41
    wi
    #
    @11
    @12
    @13
    @16
    simplrl
    @1
    @23
    @7
    @12
    @42
    wi
    wi
    #
    @3
    @1
    @39
    @8
    cch
    wcel
    #
    @6
    wa
    #
    @43
    @23
    @40
    @9
    @6
    @45
    @9
    @44
    @6
    @8
    atelch
    anim1i
    ancoms
    @39
    @44
    @6
    @43
    @39
    @44
    wa
    #
    @6
    wa
    #
    @7
    @12
    @17
    @41
    @47
    @7
    @12
    @17
    wa
    #
    wa
    wa
    @30
    @5
    cA
    chj
    co
    #
    @5
    @47
    @48
    @30
    @49
    wss
    #
    @7
    @47
    @48
    wa
    @0
    @49
    wss
    #
    @8
    @49
    wss
    #
    wa
    #
    @50
    @6
    @48
    @53
    @46
    @48
    @6
    @53
    @12
    @17
    @6
    @53
    @12
    @6
    wa
    @51
    @17
    @6
    wa
    @52
    @6
    @12
    cA
    @49
    wss
    #
    @51
    cA
    cch
    wcel
    #
    @6
    @54
    mdsymlem1.1
    cA
    @5
    chub2
    mpan
    @0
    cA
    @49
    sstr
    sylan2
    @6
    @17
    @5
    @49
    wss
    #
    @52
    @6
    @55
    @56
    mdsymlem1.1
    @5
    cA
    chub1
    mpan2
    @8
    @5
    @49
    sstr
    sylan2
    anim12i
    anandirs
    ancoms
    adantll
    @47
    @53
    @50
    wb
    #
    @48
    @39
    @44
    @6
    @57
    @6
    @39
    @44
    @49
    cch
    wcel
    #
    @57
    @6
    @55
    @58
    mdsymlem1.1
    @5
    cA
    chjcl
    mpan2
    @0
    @8
    @49
    chlub
    syl3an3
    3expa
    adantr
    mpbid
    adantrl
    @6
    @7
    @49
    @5
    wceq
    #
    @46
    @48
    @6
    @7
    @59
    @55
    @6
    @7
    @59
    wb
    mdsymlem1.1
    cA
    @5
    chlejb2
    mpan
    biimpa
    ad2ant2lr
    sseqtrd
    exp45
    anasss
    syl2an
    adantlr
    syl7
    imp44
    sstrd
    @27
    @13
    @24
    @25
    @13
    @7
    @17
    @11
    @12
    @13
    @16
    simplrr
    ad2antlr
    adantl
    ssind
    @24
    @26
    @29
    @20
    wi
    #
    @17
    @24
    @25
    @60
    @7
    @24
    @15
    @60
    @16
    @24
    @11
    @14
    @60
    @24
    @11
    wa
    @12
    @60
    @13
    @24
    @11
    @12
    @60
    @4
    @6
    @11
    @12
    @60
    wi
    wi
    #
    @9
    @4
    @39
    @2
    cch
    wcel
    #
    wa
    #
    @6
    @61
    @1
    @39
    @3
    @62
    @40
    @2
    atelch
    anim12i
    @63
    @6
    wa
    #
    @11
    @12
    @60
    @64
    @11
    @12
    wa
    wa
    @29
    @10
    @19
    wss
    #
    @20
    @64
    @12
    @29
    @65
    wi
    @11
    @64
    @12
    wa
    #
    @29
    @2
    @0
    chj
    co
    #
    @18
    @0
    chj
    co
    #
    wss
    #
    @65
    @64
    @29
    @69
    wi
    #
    @12
    @39
    @62
    @6
    @70
    @62
    @6
    @39
    @70
    @6
    @62
    @18
    cch
    wcel
    #
    @39
    @70
    @6
    cB
    cch
    wcel
    @71
    mdsymlem1.2
    @5
    cB
    chincl
    mpan2
    #
    @62
    @71
    @39
    w3a
    @29
    @69
    @2
    @18
    @0
    chlej1
    ex
    syl3an2
    3comr
    3expa
    adantr
    @66
    @69
    @67
    @19
    wss
    #
    @65
    @66
    @68
    @19
    wss
    #
    @69
    @73
    @39
    @6
    @12
    @74
    @62
    @6
    @39
    @71
    @12
    @74
    @72
    @39
    @55
    @71
    @12
    @74
    mdsymlem1.1
    @0
    cA
    @18
    chlej2
    mp3anl2
    sylanl2
    adantllr
    @67
    @68
    @19
    sstr2
    syl5com
    @66
    @10
    @67
    @19
    @63
    @10
    @67
    wceq
    @6
    @12
    @0
    @2
    chjcom
    ad2antrr
    sseq1d
    sylibrd
    syld
    adantrl
    @11
    @65
    @20
    wi
    @64
    @12
    @8
    @10
    @19
    sstr2
    ad2antrl
    syld
    exp32
    sylan
    adantrr
    imp31
    adantrr
    anasss
    adantrr
    adantrl
    adantrr
    mpd
    exp32
    exp4d
    exp32
    com34
    imp4c
    com24
end
