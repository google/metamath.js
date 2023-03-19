include "wcel.mm"
include "con0.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cuni.mm"
include "cfv.mm"
include "cv.mm"
include "ciun.mm"
include "wn.mm"
include "wa.mm"
include "wlim.mm"
include "wceq.mm"
include "word.mm"
include "ssorduni.mm"
include "ad2antrr.mm"
include "wi.mm"
include "nelneq.mm"
include "wo.mm"
include "elssuni.mm"
include "adantl.mm"
include "wb.mm"
include "ssel.mm"
include "eloni.mm"
include "syl6.mm"
include "imp.mm"
include "ordsseleq.mm"
include "syl2an.mm"
include "anabss1.mm"
include "mpbid.mm"
include "ord.mm"
include "con1d.mm"
include "syl5.mm"
include "exp4b.mm"
include "pm2.43d.mm"
include "com23.mm"
include "ssrdv.mm"
include "ssn0.mm"
include "sylan.mm"
include "unissd.mm"
include "orduniss.mm"
include "syl.mm"
include "adantr.mm"
include "eqssd.mm"
include "df-lim.mm"
include "syl3anbrc.mm"
include "an32s.mm"
include "3adantl1.mm"
include "ssonuni.mm"
include "limeq.mm"
include "fveq2.mm"
include "iuneq1.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "3adant3.mm"
include "mpd.mm"
include "wral.mm"
include "wrex.mm"
include "eluni2.mm"
include "anim1d.mm"
include "onelon.mm"
include "adantrd.mm"
include "ordelss.mm"
include "a1i.mm"
include "syland.mm"
include "3jcad.mm"
include "expd.mm"
include "reximdvai.mm"
include "syl5bi.mm"
include "ssiun.mm"
include "ralrimiv.mm"
include "iunss.mm"
include "sylibr.mm"
include "cbviunv.mm"
include "syl6sseq.mm"
include "3ad2ant2.mm"
include "eqsstrd.mm"
include "ex.mm"
include "ssiun2s.mm"
include "pm2.61d2.mm"
include "jcad.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "sseq2d.mm"
include "3com12.mm"
include "3expib.mm"
include "vtoclga.mm"
include "sylsyld.mm"

theorem onfununi
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T
  let cF: class F
  assume onfununi.1: |- ( Lim y -> ( F ` y ) = U_ x e. y ( F ` x ) )
  assume onfununi.2: |- ( ( x e. On /\ y e. On /\ x C_ y ) -> ( F ` x ) C_ ( F ` y ) )

  disjoint x y
  disjoint S x
  disjoint S y
  disjoint F x
  disjoint F y
  disjoint T x
  assert |- ( ( S e. T /\ S C_ On /\ S =/= (/) ) -> ( F ` U. S ) = U_ x e. S ( F ` x ) )

  proof
    cS
    cT
    wcel
    #
    cS
    con0
    wss
    #
    cS
    c0
    wne
    #
    w3a
    #
    cS
    cuni
    #
    cF
    cfv
    #
    vx
    cS
    vx
    cv
    #
    cF
    cfv
    #
    ciun
    #
    @3
    @4
    cS
    wcel
    #
    @5
    @8
    wss
    #
    @3
    @9
    wn
    #
    @10
    @3
    @11
    wa
    #
    @5
    vx
    @4
    @7
    ciun
    #
    @8
    @12
    @4
    wlim
    #
    @5
    @13
    wceq
    #
    @1
    @2
    @11
    @14
    @0
    @1
    @11
    @2
    @14
    @1
    @11
    wa
    #
    @2
    wa
    @4
    word
    #
    @4
    c0
    wne
    #
    @4
    @4
    cuni
    #
    wceq
    #
    @14
    @1
    @17
    @11
    @2
    cS
    ssorduni
    #
    ad2antrr
    @16
    cS
    @4
    wss
    @2
    @18
    @16
    vx
    cS
    @4
    @1
    @11
    @6
    cS
    wcel
    #
    @6
    @4
    wcel
    #
    wi
    @1
    @22
    @11
    @23
    @1
    @22
    @11
    @23
    wi
    @1
    @22
    @22
    @11
    @23
    @22
    @11
    wa
    @6
    @4
    wceq
    #
    wn
    @1
    @22
    wa
    #
    @23
    @6
    @4
    cS
    nelneq
    @25
    @23
    @24
    @25
    @23
    @24
    @25
    @6
    @4
    wss
    #
    @23
    @24
    wo
    #
    @22
    @26
    @1
    @6
    cS
    elssuni
    #
    adantl
    @1
    @22
    @26
    @27
    wb
    #
    @25
    @6
    word
    #
    @17
    @29
    @1
    @1
    @22
    @30
    @1
    @22
    @6
    con0
    wcel
    #
    @30
    cS
    con0
    @6
    ssel
    #
    @6
    eloni
    syl6
    imp
    @21
    @6
    @4
    ordsseleq
    syl2an
    anabss1
    mpbid
    ord
    con1d
    syl5
    exp4b
    pm2.43d
    com23
    imp
    ssrdv
    #
    cS
    @4
    ssn0
    sylan
    @16
    @20
    @2
    @16
    @4
    @19
    @16
    cS
    @4
    @33
    unissd
    @1
    @19
    @4
    wss
    #
    @11
    @1
    @17
    @34
    @21
    @4
    orduniss
    syl
    adantr
    eqssd
    adantr
    @4
    df-lim
    syl3anbrc
    an32s
    3adantl1
    @3
    @14
    @15
    wi
    #
    @11
    @0
    @1
    @35
    @2
    @0
    @1
    @35
    @0
    @1
    @4
    con0
    wcel
    #
    @35
    cS
    cT
    ssonuni
    #
    vy
    cv
    #
    wlim
    #
    @38
    cF
    cfv
    #
    vx
    @38
    @7
    ciun
    #
    wceq
    #
    wi
    @35
    vy
    @4
    con0
    @38
    @4
    wceq
    #
    @39
    @14
    @42
    @15
    @38
    @4
    limeq
    @43
    @40
    @5
    @41
    @13
    @38
    @4
    cF
    fveq2
    #
    vx
    @38
    @4
    @7
    iuneq1
    eqeq12d
    imbi12d
    onfununi.1
    vtoclg
    syl6
    imp
    3adant3
    adantr
    mpd
    @3
    @13
    @8
    wss
    #
    @11
    @1
    @0
    @45
    @2
    @1
    @13
    vy
    cS
    @40
    ciun
    #
    @8
    @1
    @7
    @46
    wss
    #
    vx
    @4
    wral
    @13
    @46
    wss
    @1
    @47
    vx
    @4
    @1
    @23
    @7
    @40
    wss
    #
    vy
    cS
    wrex
    #
    @47
    @23
    @6
    @38
    wcel
    #
    vy
    cS
    wrex
    @1
    @49
    vy
    @6
    cS
    eluni2
    @1
    @50
    @48
    vy
    cS
    @1
    @38
    cS
    wcel
    #
    @50
    @48
    @1
    @51
    @50
    wa
    #
    @31
    @38
    con0
    wcel
    #
    @6
    @38
    wss
    #
    w3a
    @48
    @1
    @52
    @31
    @53
    @54
    @1
    @52
    @53
    @50
    wa
    @31
    @1
    @51
    @53
    @50
    cS
    con0
    @38
    ssel
    #
    anim1d
    @38
    @6
    onelon
    syl6
    @1
    @51
    @53
    @50
    @55
    adantrd
    @1
    @51
    @38
    word
    #
    @50
    @54
    @1
    @51
    @53
    @56
    @55
    @38
    eloni
    syl6
    @56
    @50
    wa
    @54
    wi
    @1
    @38
    @6
    ordelss
    a1i
    syland
    3jcad
    onfununi.2
    syl6
    expd
    reximdvai
    syl5bi
    vy
    cS
    @40
    @7
    ssiun
    syl6
    ralrimiv
    vx
    @4
    @7
    @46
    iunss
    sylibr
    vy
    vx
    cS
    @40
    @7
    @38
    @6
    cF
    fveq2
    cbviunv
    syl6sseq
    3ad2ant2
    adantr
    eqsstrd
    ex
    vx
    cS
    @7
    @4
    @5
    @6
    @4
    cF
    fveq2
    ssiun2s
    pm2.61d2
    @3
    @7
    @5
    wss
    #
    vx
    cS
    wral
    @8
    @5
    wss
    @3
    @57
    vx
    cS
    @3
    @36
    @22
    @31
    @26
    wa
    #
    @57
    @0
    @1
    @36
    @2
    @0
    @1
    @36
    @37
    imp
    3adant3
    @3
    @22
    @31
    @26
    @1
    @0
    @22
    @31
    wi
    @2
    @32
    3ad2ant2
    @22
    @26
    wi
    @3
    @28
    a1i
    jcad
    @31
    @54
    wa
    #
    @48
    wi
    @58
    @57
    wi
    vy
    @4
    con0
    @43
    @59
    @58
    @48
    @57
    @43
    @54
    @26
    @31
    @38
    @4
    @6
    sseq2
    anbi2d
    @43
    @40
    @5
    @7
    @44
    sseq2d
    imbi12d
    @53
    @31
    @54
    @48
    @31
    @53
    @54
    @48
    onfununi.2
    3com12
    3expib
    vtoclga
    sylsyld
    ralrimiv
    vx
    cS
    @7
    @5
    iunss
    sylibr
    eqssd
end
