include "ctsk.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "ccrd.mm"
include "cfv.mm"
include "ccf.mm"
include "wceq.mm"
include "cv.mm"
include "cpw.mm"
include "csdm.mm"
include "wbr.mm"
include "wral.mm"
include "cina.mm"
include "cardeq0.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "wn.mm"
include "cmap.mm"
include "co.mm"
include "cale.mm"
include "wss.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "char.mm"
include "cmpt.mm"
include "eqid.mm"
include "pwcfsdom.mm"
include "com.mm"
include "cdom.mm"
include "vpwex.mm"
include "canth2.mm"
include "cen.mm"
include "simpl.mm"
include "cardon.mm"
include "oneli.mm"
include "adantl.mm"
include "cardsdomelir.mm"
include "tskord.mm"
include "syl3anc.mm"
include "tskpw.mm"
include "tskpwss.mm"
include "syldan.mm"
include "ssdomg.mm"
include "sylc.mm"
include "cardidg.mm"
include "ensymd.mm"
include "adantr.mm"
include "domentr.mm"
include "syl2anc.mm"
include "sdomdomtr.mm"
include "sylancr.mm"
include "ralrimiva.mm"
include "wrex.mm"
include "wi.mm"
include "inawinalem.mm"
include "ax-mp.mm"
include "winainflem.mm"
include "mp3an2.mm"
include "sylan2.mm"
include "cardidm.mm"
include "cardaleph.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "breq12d.mm"
include "mpbiri.mm"
include "w3a.mm"
include "simp1.mm"
include "simp3.mm"
include "cxp.mm"
include "wf.mm"
include "fvex.mm"
include "elmap.mm"
include "fssxp.mm"
include "sylbi.mm"
include "ex.mm"
include "ssrdv.mm"
include "cfle.mm"
include "sstr.mm"
include "mpan.mm"
include "tskxpss.mm"
include "3exp.mm"
include "com23.mm"
include "mpdi.mm"
include "mpd.mm"
include "sstr2.mm"
include "syl2im.mm"
include "simp2.mm"
include "wfn.mm"
include "cvv.mm"
include "ffn.mm"
include "fndmeng.mm"
include "ensdomtr.mm"
include "syl2an.mm"
include "tskssel.mm"
include "3expia.mm"
include "imp.mm"
include "domnsym.mm"
include "syl.mm"
include "mt2d.mm"
include "wo.mm"
include "cfon.mm"
include "onsseli.mm"
include "mpbi.mm"
include "ori.mm"
include "elina.mm"
include "syl3anbrc.mm"

theorem tskcard
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( T e. Tarski /\ T =/= (/) ) -> ( card ` T ) e. Inacc )

  proof
    cT
    ctsk
    wcel
    #
    cT
    c0
    wne
    #
    wa
    #
    cT
    ccrd
    cfv
    #
    c0
    wne
    #
    @3
    ccf
    cfv
    #
    @3
    wceq
    #
    vx
    cv
    #
    cpw
    #
    @3
    csdm
    wbr
    #
    vx
    @3
    wral
    #
    @3
    cina
    wcel
    @0
    @4
    @1
    @0
    @3
    c0
    cT
    c0
    cT
    ctsk
    cardeq0
    necon3bid
    biimpar
    #
    @2
    @5
    @3
    wcel
    #
    wn
    @6
    @2
    @12
    @3
    @3
    @5
    cmap
    co
    #
    csdm
    wbr
    #
    @2
    @14
    @3
    @7
    cale
    cfv
    wss
    vx
    con0
    crab
    cint
    #
    cale
    cfv
    #
    @16
    @16
    ccf
    cfv
    #
    cmap
    co
    #
    csdm
    wbr
    vz
    @15
    vw
    vz
    @17
    vz
    cv
    vw
    cv
    cfv
    char
    cfv
    cmpt
    #
    @19
    eqid
    pwcfsdom
    @2
    @3
    @16
    @13
    @18
    csdm
    @2
    com
    @3
    wss
    #
    @3
    ccrd
    cfv
    @3
    wceq
    @3
    @16
    wceq
    @2
    @4
    @10
    @20
    @11
    @0
    @10
    @1
    @0
    @9
    vx
    @3
    @0
    @7
    @3
    wcel
    #
    wa
    #
    @8
    @8
    cpw
    #
    csdm
    wbr
    @23
    @3
    cdom
    wbr
    #
    @9
    @8
    vx
    vpwex
    canth2
    @22
    @23
    cT
    cdom
    wbr
    #
    cT
    @3
    cen
    wbr
    #
    @24
    @22
    @0
    @23
    cT
    wss
    #
    @25
    @0
    @21
    simpl
    #
    @0
    @21
    @7
    cT
    wcel
    #
    @27
    @22
    @0
    @7
    con0
    wcel
    #
    @7
    cT
    csdm
    wbr
    #
    @29
    @28
    @21
    @30
    @0
    @3
    @7
    cT
    cardon
    #
    oneli
    adantl
    @21
    @31
    @0
    @7
    cT
    cardsdomelir
    adantl
    @7
    cT
    tskord
    syl3anc
    #
    @0
    @29
    @8
    cT
    wcel
    @27
    @7
    cT
    tskpw
    @8
    cT
    tskpwss
    syldan
    syldan
    @23
    cT
    ctsk
    ssdomg
    sylc
    @0
    @26
    @21
    @0
    @3
    cT
    cT
    ctsk
    cardidg
    ensymd
    #
    adantr
    @23
    cT
    @3
    domentr
    syl2anc
    @8
    @23
    @3
    sdomdomtr
    sylancr
    ralrimiva
    adantr
    #
    @10
    @4
    @7
    vy
    cv
    csdm
    wbr
    vy
    @3
    wrex
    vx
    @3
    wral
    #
    @20
    @3
    con0
    wcel
    #
    @10
    @36
    wi
    @32
    vx
    vy
    @3
    inawinalem
    ax-mp
    @4
    @37
    @36
    @20
    @32
    vx
    vy
    @3
    winainflem
    mp3an2
    sylan2
    syl2anc
    cT
    cardidm
    vx
    @3
    cardaleph
    sylancl
    #
    @2
    @3
    @16
    @5
    @17
    cmap
    @38
    @2
    @3
    @16
    ccf
    @38
    fveq2d
    oveq12d
    breq12d
    mpbiri
    @0
    @12
    @14
    wn
    #
    wi
    @1
    @0
    @12
    @39
    @0
    @12
    wa
    #
    @13
    @3
    cdom
    wbr
    #
    @39
    @40
    @13
    cT
    cdom
    wbr
    #
    @26
    @41
    @0
    @12
    @13
    cT
    wss
    #
    @42
    @40
    vx
    @13
    cT
    @0
    @12
    @7
    @13
    wcel
    #
    @29
    @0
    @12
    @44
    w3a
    #
    @0
    @7
    cT
    wss
    #
    @31
    @29
    @0
    @12
    @44
    simp1
    #
    @45
    @44
    @0
    @46
    @0
    @12
    @44
    simp3
    #
    @47
    @44
    @7
    @5
    @3
    cxp
    #
    wss
    #
    @0
    @49
    cT
    wss
    #
    @46
    @44
    @5
    @3
    @7
    wf
    #
    @50
    @3
    @5
    @7
    cT
    ccrd
    fvex
    @3
    ccf
    fvex
    #
    elmap
    #
    @5
    @3
    @7
    fssxp
    sylbi
    @0
    @3
    cT
    wss
    #
    @51
    @0
    vx
    @3
    cT
    @0
    @21
    @29
    @33
    ex
    ssrdv
    @0
    @55
    @5
    cT
    wss
    #
    @51
    @5
    @3
    wss
    #
    @55
    @56
    @3
    cfle
    #
    @5
    @3
    cT
    sstr
    mpan
    @0
    @56
    @55
    @51
    @0
    @56
    @55
    @51
    @5
    @3
    cT
    tskxpss
    3exp
    com23
    mpdi
    mpd
    @7
    @49
    cT
    sstr2
    syl2im
    sylc
    @45
    @44
    @12
    @31
    @48
    @0
    @12
    @44
    simp2
    @44
    @7
    @5
    cen
    wbr
    @5
    cT
    csdm
    wbr
    @31
    @12
    @44
    @5
    @7
    @44
    @52
    @5
    @7
    cen
    wbr
    #
    @54
    @52
    @7
    @5
    wfn
    @5
    cvv
    wcel
    @59
    @5
    @3
    @7
    ffn
    @53
    @5
    cvv
    @7
    fndmeng
    sylancl
    sylbi
    ensymd
    @5
    cT
    cardsdomelir
    @7
    @5
    cT
    ensdomtr
    syl2an
    syl2anc
    @7
    cT
    tskssel
    syl3anc
    3expia
    ssrdv
    @0
    @43
    @42
    @13
    cT
    ctsk
    ssdomg
    imp
    syldan
    @0
    @26
    @12
    @34
    adantr
    @13
    cT
    @3
    domentr
    syl2anc
    @13
    @3
    domnsym
    syl
    ex
    adantr
    mt2d
    @12
    @6
    @57
    @12
    @6
    wo
    @58
    @5
    @3
    @3
    cfon
    @32
    onsseli
    mpbi
    ori
    syl
    @35
    vx
    @3
    elina
    syl3anbrc
end
