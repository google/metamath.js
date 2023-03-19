include "cv.mm"
include "cat.mm"
include "wcel.mm"
include "cin.mm"
include "wss.mm"
include "wn.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "c0h.mm"
include "wne.mm"
include "wrex.mm"
include "wi.mm"
include "ssin.mm"
include "sseq2i.mm"
include "biimpi.mm"
include "adantl.mm"
include "sylbir.mm"
include "atcvat4i.mm"
include "exp4b.mm"
include "com34.mm"
include "com23.mm"
include "imp4b.mm"
include "sylan2.mm"
include "adantrr.mm"
include "com12.mm"
include "adantlr.mm"
include "imp.mm"
include "wceq.mm"
include "nssne2.mm"
include "adantrl.mm"
include "wb.mm"
include "atnemeq0.mm"
include "ancoms.mm"
include "syl5ib.mm"
include "adantll.mm"
include "adantr.mm"
include "cch.mm"
include "atelch.mm"
include "chjcom.mm"
include "syl2an.mm"
include "sseq2d.mm"
include "atexch.mm"
include "syl3an1.mm"
include "3com13.mm"
include "3expa.mm"
include "expd.mm"
include "sylbid.mm"
include "syld.mm"
include "exp31.mm"
include "com24.mm"
include "impd.mm"
include "anasss.mm"
include "simprl.mm"
include "a1i.mm"
include "simpl.mm"
include "ad2antrl.mm"
include "jctird.mm"
include "jcad.mm"
include "reximdvai.mm"
include "mpd.mm"
include "chjcl.mm"
include "mpan.mm"
include "syl5eqel.mm"
include "chincl.mm"
include "sylancr.mm"
include "syl.mm"
include "chrelat2.mm"
include "sylancl.mm"
include "biimpa.mm"
include "ad2antrr.mm"
include "reximddv.mm"

theorem mdsymlem3
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
  disjoint p q
  disjoint p r
  disjoint A p
  disjoint A q
  disjoint A r
  disjoint B p
  disjoint B q
  disjoint B r
  disjoint c p
  disjoint c q
  disjoint c r
  disjoint A c
  disjoint B c
  assert |- ( ( ( ( p e. HAtoms /\ -. ( B i^i C ) C_ A ) /\ p C_ ( A vH B ) ) /\ A =/= 0H ) -> E. r e. HAtoms E. q e. HAtoms ( p C_ ( q vH r ) /\ ( q C_ A /\ r C_ B ) ) )

  proof
    vp
    cv
    #
    cat
    wcel
    #
    cB
    cC
    cin
    #
    cA
    wss
    wn
    #
    wa
    #
    @0
    cA
    cB
    chj
    co
    wss
    #
    wa
    #
    cA
    c0h
    wne
    #
    wa
    #
    vr
    cv
    #
    @2
    wss
    #
    @9
    cA
    wss
    wn
    #
    wa
    #
    @0
    vq
    cv
    #
    @9
    chj
    co
    wss
    #
    @13
    cA
    wss
    #
    @9
    cB
    wss
    #
    wa
    #
    wa
    #
    vq
    cat
    wrex
    #
    vr
    cat
    @8
    @9
    cat
    wcel
    #
    @12
    wa
    #
    wa
    #
    @15
    @9
    @0
    @13
    chj
    co
    #
    wss
    #
    wa
    #
    vq
    cat
    wrex
    #
    @19
    @8
    @21
    @26
    @4
    @7
    @21
    @26
    wi
    #
    @5
    @1
    @7
    @27
    @3
    @21
    @1
    @7
    wa
    #
    @26
    @20
    @10
    @28
    @26
    wi
    #
    @11
    @10
    @20
    @9
    cA
    @0
    chj
    co
    #
    wss
    #
    @29
    @10
    @16
    @9
    cC
    wss
    #
    wa
    #
    @31
    @9
    cB
    cC
    ssin
    #
    @32
    @31
    @16
    @32
    @31
    cC
    @30
    @9
    mdsymlem1.3
    sseq2i
    biimpi
    adantl
    sylbir
    @20
    @31
    @1
    @7
    @26
    @20
    @1
    @31
    @7
    @26
    wi
    @20
    @1
    @7
    @31
    @26
    @20
    @1
    @7
    @31
    @26
    vq
    cA
    @9
    @0
    mdsymlem1.1
    atcvat4i
    exp4b
    com34
    com23
    imp4b
    sylan2
    adantrr
    com12
    adantlr
    adantlr
    imp
    @22
    @25
    @18
    vq
    cat
    @6
    @21
    @13
    cat
    wcel
    #
    @25
    @18
    wi
    wi
    #
    @7
    @4
    @21
    @36
    @5
    @1
    @21
    @36
    @3
    @1
    @21
    wa
    #
    @35
    @25
    @18
    @37
    @35
    @25
    wa
    #
    @14
    @17
    @1
    @20
    @12
    @38
    @14
    wi
    @1
    @20
    wa
    #
    @12
    @35
    @25
    @14
    @39
    @25
    @35
    @12
    @14
    @39
    @15
    @24
    @35
    @12
    @14
    wi
    #
    wi
    @39
    @35
    @24
    @15
    @40
    @39
    @35
    @24
    @15
    @40
    wi
    @39
    @35
    wa
    #
    @24
    wa
    #
    @15
    @12
    @14
    @42
    @15
    @12
    wa
    #
    @13
    @9
    cin
    c0h
    wceq
    #
    @14
    @41
    @43
    @44
    wi
    #
    @24
    @20
    @35
    @45
    @1
    @43
    @13
    @9
    wne
    #
    @20
    @35
    wa
    @44
    @15
    @11
    @46
    @10
    @13
    @9
    cA
    nssne2
    adantrl
    @35
    @20
    @46
    @44
    wb
    @13
    @9
    atnemeq0
    ancoms
    syl5ib
    adantll
    adantr
    @41
    @24
    @44
    @14
    wi
    #
    @41
    @24
    @9
    @13
    @0
    chj
    co
    #
    wss
    #
    @47
    @41
    @23
    @48
    @9
    @1
    @35
    @23
    @48
    wceq
    #
    @20
    @1
    @0
    cch
    wcel
    #
    @13
    cch
    wcel
    #
    @50
    @35
    @0
    atelch
    #
    @13
    atelch
    #
    @0
    @13
    chjcom
    syl2an
    adantlr
    sseq2d
    @41
    @49
    @44
    @14
    @1
    @20
    @35
    @49
    @44
    wa
    @14
    wi
    #
    @35
    @20
    @1
    @55
    @35
    @52
    @20
    @1
    @55
    @54
    @13
    @9
    @0
    atexch
    syl3an1
    3com13
    3expa
    expd
    sylbid
    imp
    syld
    expd
    exp31
    com24
    impd
    com24
    imp4b
    anasss
    @37
    @38
    @15
    @16
    @38
    @15
    wi
    @37
    @35
    @15
    @24
    simprl
    a1i
    @21
    @16
    @1
    @10
    @16
    @20
    @11
    @10
    @33
    @16
    @34
    @16
    @32
    simpl
    sylbir
    ad2antrl
    adantl
    jctird
    jcad
    expd
    adantlr
    adantlr
    adantlr
    reximdvai
    mpd
    @4
    @12
    vr
    cat
    wrex
    #
    @5
    @7
    @1
    @3
    @56
    @1
    @2
    cch
    wcel
    #
    cA
    cch
    wcel
    #
    @3
    @56
    wb
    @1
    @51
    @57
    @53
    @51
    cB
    cch
    wcel
    cC
    cch
    wcel
    @57
    mdsymlem1.2
    @51
    cC
    @30
    cch
    mdsymlem1.3
    @58
    @51
    @30
    cch
    wcel
    mdsymlem1.1
    cA
    @0
    chjcl
    mpan
    syl5eqel
    cB
    cC
    chincl
    sylancr
    syl
    mdsymlem1.1
    vr
    @2
    cA
    chrelat2
    sylancl
    biimpa
    ad2antrr
    reximddv
end
