include "ctop.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "wa.mm"
include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "csn.mm"
include "cnei.mm"
include "wral.mm"
include "wss.mm"
include "wrex.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "3ad2ant3.mm"
include "ad2antrr.mm"
include "neii2.mm"
include "3ad2antl2.mm"
include "ad2ant2rl.mm"
include "simpll.mm"
include "simprl.mm"
include "fvex.mm"
include "snss.mm"
include "biimpri.mm"
include "adantr.mm"
include "ad2antll.mm"
include "3jca.mm"
include "adantll.mm"
include "cnpimaex.mm"
include "syl.mm"
include "wi.mm"
include "sstr2.mm"
include "com12.mm"
include "ad2antlr.mm"
include "wfun.mm"
include "wb.mm"
include "ffun.mm"
include "eltopss.mm"
include "adantlr.mm"
include "sseq2d.mm"
include "mpbird.mm"
include "3adantl2.mm"
include "funimass3.mm"
include "syl2anc.mm"
include "sylibd.mm"
include "anim2d.mm"
include "reximdva.mm"
include "mpd.mm"
include "rexlimddv.mm"
include "isneip.mm"
include "3ad2antl1.mm"
include "mpbir2and.mm"
include "exp32.mm"
include "ralrimdv.mm"
include "simpll3.mm"
include "opnneip.mm"
include "weq.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "3com23.mm"
include "3expb.mm"
include "ex.mm"
include "3ad2ant1.mm"
include "snssg.mm"
include "ad3antlr.mm"
include "ad3antrrr.mm"
include "biimpar.mm"
include "syldan.mm"
include "anbi12d.mm"
include "biimprd.mm"
include "3syld.mm"
include "com24.mm"
include "imp.mm"
include "ralrimiv.mm"
include "iscnp2.mm"
include "baib.mm"
include "3expa.mm"
include "3adantl3.mm"
include "impbid.mm"

theorem cnpnei
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vo: setvar o
  assume cnpnei.1: |- X = U. J
  assume cnpnei.2: |- Y = U. K

  disjoint A y
  disjoint F y
  disjoint J y
  disjoint K y
  disjoint X y
  disjoint Y y
  disjoint g o
  disjoint g y
  disjoint A g
  disjoint o y
  disjoint A o
  disjoint F g
  disjoint F o
  disjoint J g
  disjoint J o
  disjoint K g
  disjoint K o
  disjoint X g
  disjoint X o
  disjoint Y g
  disjoint Y o
  assert |- ( ( ( J e. Top /\ K e. Top /\ F : X --> Y ) /\ A e. X ) -> ( F e. ( ( J CnP K ) ` A ) <-> A. y e. ( ( nei ` K ) ` { ( F ` A ) } ) ( `' F " y ) e. ( ( nei ` J ) ` { A } ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    cX
    cY
    cF
    wf
    #
    w3a
    #
    cA
    cX
    wcel
    #
    wa
    #
    cF
    cA
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    cF
    ccnv
    #
    vy
    cv
    #
    cima
    #
    cA
    csn
    #
    cJ
    cnei
    cfv
    cfv
    #
    wcel
    #
    vy
    cA
    cF
    cfv
    #
    csn
    #
    cK
    cnei
    cfv
    cfv
    #
    wral
    #
    @5
    @6
    @12
    vy
    @15
    @5
    @6
    @8
    @15
    wcel
    #
    @12
    @5
    @6
    @17
    wa
    #
    wa
    #
    @12
    @9
    cX
    wss
    #
    cA
    vo
    cv
    #
    wcel
    #
    @21
    @9
    wss
    #
    wa
    #
    vo
    cJ
    wrex
    #
    @3
    @20
    @4
    @18
    @2
    @0
    @20
    @1
    @2
    cF
    cdm
    #
    @9
    cX
    cF
    @8
    cnvimass
    cX
    cY
    cF
    fdm
    #
    syl5sseq
    3ad2ant3
    ad2antrr
    @19
    @14
    vg
    cv
    #
    wss
    #
    @28
    @8
    wss
    #
    wa
    #
    @25
    vg
    cK
    @3
    @17
    @31
    vg
    cK
    wrex
    #
    @4
    @6
    @1
    @0
    @17
    @32
    @2
    @14
    vg
    cK
    @8
    neii2
    3ad2antl2
    ad2ant2rl
    @19
    @28
    cK
    wcel
    #
    @31
    wa
    #
    wa
    #
    @22
    cF
    @21
    cima
    #
    @28
    wss
    #
    wa
    #
    vo
    cJ
    wrex
    #
    @25
    @35
    @6
    @33
    @13
    @28
    wcel
    #
    w3a
    #
    @39
    @18
    @34
    @41
    @5
    @18
    @34
    wa
    @6
    @33
    @40
    @6
    @17
    @34
    simpll
    @18
    @33
    @31
    simprl
    @31
    @40
    @18
    @33
    @29
    @40
    @30
    @40
    @29
    @13
    @28
    cA
    cF
    fvex
    snss
    biimpri
    adantr
    ad2antll
    3jca
    adantll
    vo
    @28
    cA
    cF
    cJ
    cK
    cnpimaex
    syl
    @35
    @38
    @24
    vo
    cJ
    @35
    @21
    cJ
    wcel
    #
    wa
    #
    @37
    @23
    @22
    @43
    @37
    @36
    @8
    wss
    #
    @23
    @34
    @37
    @44
    wi
    #
    @19
    @42
    @30
    @45
    @33
    @29
    @37
    @30
    @44
    @36
    @28
    @8
    sstr2
    com12
    ad2antll
    ad2antlr
    @43
    cF
    wfun
    #
    @21
    @26
    wss
    #
    @44
    @23
    wb
    @19
    @46
    @34
    @42
    @3
    @46
    @4
    @18
    @2
    @0
    @46
    @1
    cX
    cY
    cF
    ffun
    3ad2ant3
    #
    ad2antrr
    ad2antrr
    @19
    @42
    @47
    @34
    @5
    @42
    @47
    @18
    @3
    @42
    @47
    @4
    @0
    @2
    @42
    @47
    @1
    @0
    @2
    wa
    @42
    wa
    @47
    @21
    cX
    wss
    #
    @0
    @42
    @49
    @2
    @21
    cJ
    cX
    cnpnei.1
    eltopss
    adantlr
    @2
    @47
    @49
    wb
    @0
    @42
    @2
    @26
    cX
    @21
    @27
    sseq2d
    ad2antlr
    mpbird
    3adantl2
    adantlr
    adantlr
    adantlr
    @21
    @8
    cF
    funimass3
    syl2anc
    sylibd
    anim2d
    reximdva
    mpd
    rexlimddv
    @5
    @12
    @20
    @25
    wa
    wb
    #
    @18
    @0
    @1
    @4
    @50
    @2
    cA
    vo
    cJ
    @9
    cX
    cnpnei.1
    isneip
    3ad2antl1
    adantr
    mpbir2and
    exp32
    ralrimdv
    @5
    @16
    @6
    @5
    @16
    wa
    #
    @6
    @2
    @13
    @21
    wcel
    #
    cA
    @28
    wcel
    #
    cF
    @28
    cima
    @21
    wss
    #
    wa
    #
    vg
    cJ
    wrex
    #
    wi
    #
    vo
    cK
    wral
    #
    @0
    @1
    @2
    @4
    @16
    simpll3
    @51
    @57
    vo
    cK
    @5
    @16
    @21
    cK
    wcel
    #
    @57
    wi
    @5
    @52
    @59
    @16
    @56
    @5
    @52
    @59
    @16
    @56
    wi
    @5
    @52
    @59
    wa
    #
    wa
    #
    @16
    @7
    @21
    cima
    #
    @11
    wcel
    #
    @10
    @28
    wss
    #
    @28
    @62
    wss
    #
    wa
    #
    vg
    cJ
    wrex
    #
    @56
    @3
    @60
    @16
    @63
    wi
    #
    @4
    @1
    @0
    @60
    @68
    @2
    @1
    @52
    @59
    @68
    @1
    @59
    @52
    @68
    @1
    @59
    @52
    w3a
    @21
    @15
    wcel
    @68
    @13
    cK
    @21
    opnneip
    @12
    @63
    vy
    @21
    @15
    vy
    vo
    weq
    @9
    @62
    @11
    @8
    @21
    @7
    imaeq2
    eleq1d
    rspcv
    syl
    3com23
    3expb
    3ad2antl2
    adantlr
    @3
    @63
    @67
    wi
    #
    @4
    @60
    @0
    @1
    @69
    @2
    @0
    @63
    @67
    @10
    vg
    cJ
    @62
    neii2
    ex
    3ad2ant1
    ad2antrr
    @61
    @66
    @55
    vg
    cJ
    @61
    @28
    cJ
    wcel
    #
    wa
    #
    @55
    @66
    @71
    @53
    @64
    @54
    @65
    @4
    @53
    @64
    wb
    @3
    @60
    @70
    cA
    @28
    cX
    snssg
    ad3antlr
    @71
    @46
    @28
    @26
    wss
    #
    @54
    @65
    wb
    @3
    @46
    @4
    @60
    @70
    @48
    ad3antrrr
    @5
    @70
    @72
    @60
    @3
    @70
    @72
    @4
    @3
    @70
    @28
    cX
    wss
    #
    @72
    @0
    @1
    @70
    @73
    @2
    @28
    cJ
    cX
    cnpnei.1
    eltopss
    3ad2antl1
    @3
    @72
    @73
    @2
    @0
    @72
    @73
    wb
    @1
    @2
    @26
    cX
    @28
    @27
    sseq2d
    3ad2ant3
    biimpar
    syldan
    adantlr
    adantlr
    @28
    @21
    cF
    funimass3
    syl2anc
    anbi12d
    biimprd
    reximdva
    3syld
    exp32
    com24
    imp
    ralrimiv
    @5
    @6
    @2
    @58
    wa
    #
    wb
    #
    @16
    @0
    @1
    @4
    @75
    @2
    @0
    @1
    @4
    @75
    @6
    @0
    @1
    @4
    w3a
    @74
    vg
    vo
    cA
    cF
    cJ
    cK
    cX
    cY
    cnpnei.1
    cnpnei.2
    iscnp2
    baib
    3expa
    3adantl3
    adantr
    mpbir2and
    ex
    impbid
end
