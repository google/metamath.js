include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "wrex.mm"
include "c1.mm"
include "wcel.mm"
include "w3a.mm"
include "ccsh.mm"
include "wi.mm"
include "wceq.mm"
include "wral.mm"
include "wn.mm"
include "df-ne.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "wa.mm"
include "w3o.mm"
include "cfz.mm"
include "simpll.mm"
include "fzo0ss1.mm"
include "fzossfz.mm"
include "sstri.mm"
include "sseli.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "creps.mm"
include "cword.mm"
include "cprime.mm"
include "cmo.mm"
include "wo.mm"
include "cz.mm"
include "adantr.mm"
include "elfzelz.mm"
include "adantl.mm"
include "cshwsidrepswmod0.mm"
include "syl3anc.mm"
include "ex.mm"
include "3imp.mm"
include "olc.mm"
include "a1d.mm"
include "fzofzim.mm"
include "zmodidfzoimp.mm"
include "eqtr2.mm"
include "syl.mm"
include "expcom.mm"
include "com24.mm"
include "impcom.mm"
include "3adant3.mm"
include "orcd.mm"
include "pm2.61ine.mm"
include "df-3or.mm"
include "sylibr.mm"
include "3mix3.mm"
include "jaoi.mm"
include "mpcom.mm"
include "syl3an1.mm"
include "3mix1.mm"
include "3mix2.mm"
include "wb.mm"
include "repswsymballbi.mm"
include "3ad2ant1.mm"
include "biimpa.mm"
include "3mix3d.mm"
include "3jaoi.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "elfzo1.mm"
include "nnne0.mm"
include "pm2.21.mm"
include "sylbi.mm"
include "com12.mm"
include "cr.mm"
include "nnre.mm"
include "ltne.mm"
include "sylan.mm"
include "eqcom.mm"
include "syl5bi.mm"
include "3adant2.mm"
include "ax-1.mm"
include "pm2.24d.mm"
include "exp31.mm"
include "com34.mm"
include "com23.mm"

theorem cshwshashlem1
  let wph: wff ph
  let vi: setvar i
  let cL: class L
  let cV: class V
  let cW: class W
  let vj: setvar j
  assume cshwshash.0: |- ( ph -> ( W e. Word V /\ ( # ` W ) e. Prime ) )

  disjoint L i
  disjoint V i
  disjoint W i
  disjoint i ph
  disjoint L j
  disjoint i j
  disjoint V j
  disjoint W j
  disjoint j ph
  assert |- ( ( ph /\ E. i e. ( 0 ..^ ( # ` W ) ) ( W ` i ) =/= ( W ` 0 ) /\ L e. ( 1 ..^ ( # ` W ) ) ) -> ( W cyclShift L ) =/= W )

  proof
    wph
    vi
    cv
    cW
    cfv
    #
    cc0
    cW
    cfv
    #
    wne
    #
    vi
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    wrex
    #
    cL
    c1
    @3
    cfzo
    co
    #
    wcel
    #
    w3a
    #
    cW
    cL
    ccsh
    co
    #
    cW
    wne
    #
    wi
    @9
    cW
    @8
    @9
    cW
    wceq
    #
    @10
    wph
    @5
    @7
    @11
    @10
    wi
    #
    @5
    @0
    @1
    wceq
    #
    vi
    @4
    wral
    #
    wn
    #
    wph
    @7
    @12
    wi
    @5
    @13
    wn
    #
    vi
    @4
    wrex
    @15
    @2
    @16
    vi
    @4
    @0
    @1
    df-ne
    rexbii
    @13
    vi
    @4
    rexnal
    bitri
    wph
    @7
    @15
    @12
    wph
    @7
    @11
    @15
    @10
    wph
    @7
    @11
    @15
    @10
    wi
    wph
    @7
    wa
    #
    @11
    wa
    #
    @14
    @10
    cL
    cc0
    wceq
    #
    cL
    @3
    wceq
    #
    @14
    w3o
    #
    @18
    @14
    @18
    wph
    cL
    cc0
    @3
    cfz
    co
    #
    wcel
    #
    @11
    @21
    wph
    @7
    @11
    simpll
    @7
    @23
    wph
    @11
    @6
    @22
    cL
    @6
    @4
    @22
    @3
    fzo0ss1
    cc0
    @3
    fzossfz
    sstri
    sseli
    ad2antlr
    @17
    @11
    simpr
    @19
    @20
    cW
    @1
    @3
    creps
    co
    wceq
    #
    w3o
    #
    wph
    @23
    @11
    w3a
    #
    @21
    wph
    cW
    cV
    cword
    wcel
    #
    @3
    cprime
    wcel
    #
    wa
    #
    @23
    @11
    @25
    cshwshash.0
    cL
    @3
    cmo
    co
    #
    cc0
    wceq
    #
    @24
    wo
    #
    @29
    @23
    @11
    w3a
    #
    @25
    @29
    @23
    @11
    @32
    @29
    @23
    @11
    @32
    wi
    #
    @29
    @23
    wa
    @27
    @28
    cL
    cz
    wcel
    #
    @34
    @27
    @28
    @23
    simpll
    @29
    @28
    @23
    @27
    @28
    simpr
    adantr
    @23
    @35
    @29
    cL
    cc0
    @3
    elfzelz
    adantl
    cL
    cV
    cW
    cshwsidrepswmod0
    syl3anc
    ex
    3imp
    @31
    @33
    @25
    wi
    @24
    @31
    @33
    @25
    @31
    @33
    wa
    #
    @19
    @20
    wo
    #
    @24
    wo
    @25
    @36
    @37
    @24
    @36
    @37
    wi
    cL
    @3
    @20
    @37
    @36
    @20
    @19
    olc
    a1d
    cL
    @3
    wne
    #
    @36
    @37
    @38
    @36
    wa
    @19
    @20
    @36
    @38
    @19
    @33
    @31
    @38
    @19
    wi
    #
    @29
    @23
    @31
    @39
    wi
    #
    @11
    @23
    @29
    @40
    @23
    @38
    @31
    @29
    @19
    @38
    @23
    @31
    @29
    @19
    wi
    #
    wi
    #
    @38
    @23
    wa
    cL
    @4
    wcel
    #
    @42
    cL
    @3
    fzofzim
    @43
    @30
    cL
    wceq
    #
    @42
    cL
    @3
    zmodidfzoimp
    @44
    @31
    @41
    @44
    @31
    wa
    @19
    @29
    @30
    cL
    cc0
    eqtr2
    a1d
    ex
    syl
    syl
    expcom
    com24
    impcom
    3adant3
    impcom
    impcom
    orcd
    ex
    pm2.61ine
    orcd
    @19
    @20
    @24
    df-3or
    sylibr
    ex
    @24
    @25
    @33
    @24
    @19
    @20
    3mix3
    a1d
    jaoi
    mpcom
    syl3an1
    @19
    @26
    @21
    wi
    @20
    @24
    @19
    @21
    @26
    @19
    @20
    @14
    3mix1
    a1d
    @20
    @21
    @26
    @20
    @19
    @14
    3mix2
    a1d
    @26
    @24
    @21
    @26
    @24
    wa
    @14
    @19
    @20
    @26
    @24
    @14
    wph
    @23
    @24
    @14
    wb
    #
    @11
    wph
    @29
    @45
    cshwshash.0
    @27
    @45
    @28
    vi
    cV
    cW
    repswsymballbi
    adantr
    syl
    3ad2ant1
    biimpa
    3mix3d
    expcom
    3jaoi
    mpcom
    syl3anc
    @19
    @18
    @14
    wi
    @20
    @14
    @18
    @19
    @14
    @7
    @19
    @14
    wi
    #
    wph
    @11
    @7
    cL
    cn
    wcel
    #
    @3
    cn
    wcel
    #
    cL
    @3
    clt
    wbr
    #
    w3a
    #
    @46
    @3
    cL
    elfzo1
    #
    @47
    @48
    @46
    @49
    @47
    cL
    cc0
    wne
    #
    @46
    cL
    nnne0
    @52
    @19
    wn
    @46
    cL
    cc0
    df-ne
    @19
    @14
    pm2.21
    sylbi
    syl
    3ad2ant1
    sylbi
    ad2antlr
    com12
    @18
    @20
    @14
    @7
    @20
    @14
    wi
    #
    wph
    @11
    @7
    @50
    @53
    @51
    @47
    @49
    @53
    @48
    @47
    @49
    wa
    @3
    cL
    wne
    #
    @53
    @47
    cL
    cr
    wcel
    @49
    @54
    cL
    nnre
    cL
    @3
    ltne
    sylan
    @54
    @3
    cL
    wceq
    #
    wn
    #
    @53
    @3
    cL
    df-ne
    @20
    @55
    @56
    @14
    cL
    @3
    eqcom
    @55
    @14
    pm2.21
    syl5bi
    sylbi
    syl
    3adant2
    sylbi
    ad2antlr
    com12
    @14
    @18
    ax-1
    3jaoi
    mpcom
    pm2.24d
    exp31
    com34
    com23
    syl5bi
    3imp
    com12
    @10
    @8
    ax-1
    pm2.61ine
end
