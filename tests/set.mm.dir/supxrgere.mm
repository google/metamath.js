include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cpnf.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "wcel.mm"
include "rexr.mm"
include "pnfxr.mm"
include "a1i.mm"
include "ltpnf.mm"
include "xrltled.mm"
include "syl.mm"
include "adantr.mm"
include "id.mm"
include "eqcomd.mm"
include "adantl.mm"
include "breqtrd.mm"
include "wn.mm"
include "simpl.mm"
include "cmnf.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cv.mm"
include "wrex.mm"
include "crp.mm"
include "1rp.mm"
include "wi.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfan.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "breq1d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "vtoclgf.mm"
include "ax-mp.mm"
include "mpan2.mm"
include "w3a.mm"
include "mnfxr.mm"
include "sselda.mm"
include "3adant3.mm"
include "wss.mm"
include "supxrcl.mm"
include "3ad2ant1.mm"
include "peano2rem.mm"
include "rexrd.mm"
include "3ad2antl1.mm"
include "simpl3.mm"
include "simpr.mm"
include "wb.mm"
include "xrlenlt.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "3adantl3.mm"
include "xrltletrd.mm"
include "nltmnf.mm"
include "condan.mm"
include "supxrub.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "nltpnft.mm"
include "mtbid.mm"
include "notnotrd.mm"
include "jca.mm"
include "xrrebnd.mm"
include "simprd.mm"
include "ad2antrr.mm"
include "ltnled.mm"
include "simpll.mm"
include "resubcld.mm"
include "cc0.mm"
include "posdifd.mm"
include "mpbid.mm"
include "elrpd.mm"
include "cvv.mm"
include "ovex.mm"
include "cc.mm"
include "recnd.mm"
include "ad3antrrr.mm"
include "nncand.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "reximdva.mm"
include "wral.mm"
include "xrlenltd.mm"
include "ralrimiva.mm"
include "ralnex.mm"
include "sylib.mm"
include "pm2.61dan.mm"

theorem supxrgere
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume supxrgere.xph: |- F/ x ph
  assume supxrgere.a: |- ( ph -> A C_ RR* )
  assume supxrgere.b: |- ( ph -> B e. RR )
  assume supxrgere.y: |- ( ( ph /\ x e. RR+ ) -> E. y e. A ( B - x ) < y )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ph y
  assert |- ( ph -> B <_ sup ( A , RR* , < ) )

  proof
    wph
    cA
    cxr
    clt
    csup
    #
    cpnf
    wceq
    #
    cB
    @0
    cle
    wbr
    #
    wph
    @1
    wa
    cB
    cpnf
    @0
    cle
    wph
    cB
    cpnf
    cle
    wbr
    #
    @1
    wph
    cB
    cr
    wcel
    #
    @3
    supxrgere.b
    @4
    cB
    cpnf
    cB
    rexr
    cpnf
    cxr
    wcel
    @4
    pnfxr
    a1i
    cB
    ltpnf
    xrltled
    syl
    adantr
    @1
    cpnf
    @0
    wceq
    wph
    @1
    @0
    cpnf
    @1
    id
    eqcomd
    adantl
    breqtrd
    wph
    @1
    wn
    #
    wa
    #
    wph
    @0
    cr
    wcel
    #
    @2
    wph
    @5
    simpl
    @6
    @7
    cmnf
    @0
    clt
    wbr
    #
    @0
    cpnf
    clt
    wbr
    #
    wa
    #
    @6
    @8
    @9
    @6
    cB
    c1
    cmin
    co
    #
    vy
    cv
    #
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    @8
    wph
    @14
    @5
    wph
    c1
    crp
    wcel
    #
    @14
    1rp
    @15
    wph
    @15
    wa
    #
    @14
    wi
    #
    1rp
    wph
    vx
    cv
    #
    crp
    wcel
    #
    wa
    #
    cB
    @18
    cmin
    co
    #
    @12
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    wi
    #
    @17
    vx
    c1
    crp
    vx
    c1
    nfcv
    @16
    @14
    vx
    wph
    @15
    vx
    supxrgere.xph
    @15
    vx
    nfv
    nfan
    @14
    vx
    nfv
    nfim
    @18
    c1
    wceq
    #
    @20
    @16
    @23
    @14
    @25
    @19
    @15
    wph
    @18
    c1
    crp
    eleq1
    anbi2d
    @25
    @22
    @13
    vy
    cA
    @25
    @21
    @11
    @12
    clt
    @18
    c1
    cB
    cmin
    oveq2
    breq1d
    rexbidv
    imbi12d
    supxrgere.y
    vtoclgf
    ax-mp
    mpan2
    adantr
    @6
    @13
    @8
    vy
    cA
    wph
    @12
    cA
    wcel
    #
    @13
    @8
    wi
    wi
    @5
    wph
    @26
    @13
    @8
    wph
    @26
    @13
    w3a
    #
    cmnf
    @12
    @0
    cmnf
    cxr
    wcel
    #
    @27
    mnfxr
    a1i
    wph
    @26
    @12
    cxr
    wcel
    #
    @13
    wph
    cA
    cxr
    @12
    supxrgere.a
    sselda
    #
    3adant3
    #
    wph
    @26
    @0
    cxr
    wcel
    #
    @13
    wph
    cA
    cxr
    wss
    #
    @32
    supxrgere.a
    cA
    supxrcl
    #
    syl
    #
    3ad2ant1
    @27
    cmnf
    @12
    clt
    wbr
    #
    @11
    cmnf
    clt
    wbr
    #
    @27
    @36
    wn
    #
    wa
    #
    @11
    @12
    cmnf
    wph
    @26
    @38
    @11
    cxr
    wcel
    #
    @13
    wph
    @40
    @38
    wph
    @11
    wph
    @4
    @11
    cr
    wcel
    supxrgere.b
    cB
    peano2rem
    syl
    rexrd
    #
    adantr
    3ad2antl1
    @27
    @29
    @38
    @31
    adantr
    @28
    @39
    mnfxr
    a1i
    wph
    @26
    @13
    @38
    simpl3
    wph
    @26
    @38
    @12
    cmnf
    cle
    wbr
    #
    @13
    wph
    @26
    wa
    #
    @38
    wa
    #
    @42
    @38
    @43
    @38
    simpr
    @44
    @29
    @28
    @42
    @38
    wb
    @43
    @29
    @38
    @30
    adantr
    @28
    @44
    mnfxr
    a1i
    @12
    cmnf
    xrlenlt
    syl2anc
    mpbird
    3adantl3
    xrltletrd
    wph
    @26
    @38
    @37
    wn
    #
    @13
    wph
    @45
    @38
    wph
    @40
    @45
    @41
    @11
    nltmnf
    syl
    adantr
    3ad2antl1
    condan
    wph
    @26
    @12
    @0
    cle
    wbr
    #
    @13
    @43
    @33
    @26
    @46
    wph
    @33
    @26
    supxrgere.a
    adantr
    #
    wph
    @26
    simpr
    cA
    @12
    supxrub
    syl2anc
    #
    3adant3
    xrltletrd
    3exp
    adantr
    rexlimdv
    mpd
    @6
    @9
    @6
    @1
    @9
    wn
    #
    wph
    @5
    simpr
    wph
    @1
    @49
    wb
    #
    @5
    wph
    @32
    @50
    @35
    @0
    nltpnft
    syl
    adantr
    mtbid
    notnotrd
    jca
    @6
    @32
    @7
    @10
    wb
    wph
    @32
    @5
    @35
    adantr
    @0
    xrrebnd
    syl
    mpbird
    wph
    @7
    wa
    #
    @2
    @0
    @12
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    @51
    @2
    wn
    #
    wa
    #
    @51
    @0
    cB
    clt
    wbr
    #
    @53
    @51
    @54
    simpl
    #
    @55
    @56
    @54
    @51
    @54
    simpr
    @55
    @0
    cB
    @55
    wph
    @7
    @57
    simprd
    wph
    @4
    @7
    @54
    supxrgere.b
    ad2antrr
    ltnled
    mpbird
    @51
    @56
    wa
    #
    cB
    cB
    @0
    cmin
    co
    #
    cmin
    co
    #
    @12
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    @53
    @58
    wph
    @59
    crp
    wcel
    #
    @62
    wph
    @7
    @56
    simpll
    #
    @58
    @59
    @51
    @59
    cr
    wcel
    @56
    @51
    cB
    @0
    wph
    @4
    @7
    supxrgere.b
    adantr
    wph
    @7
    simpr
    #
    resubcld
    adantr
    @58
    @56
    cc0
    @59
    clt
    wbr
    @51
    @56
    simpr
    @58
    @0
    cB
    @51
    @7
    @56
    @65
    adantr
    @58
    wph
    @4
    @64
    supxrgere.b
    syl
    posdifd
    mpbid
    elrpd
    @59
    cvv
    wcel
    wph
    @63
    wa
    #
    @62
    wi
    #
    cB
    @0
    cmin
    ovex
    @24
    @67
    vx
    @59
    cvv
    vx
    @59
    nfcv
    @66
    @62
    vx
    wph
    @63
    vx
    supxrgere.xph
    @63
    vx
    nfv
    nfan
    @62
    vx
    nfv
    nfim
    @18
    @59
    wceq
    #
    @20
    @66
    @23
    @62
    @68
    @19
    @63
    wph
    @18
    @59
    crp
    eleq1
    anbi2d
    @68
    @22
    @61
    vy
    cA
    @68
    @21
    @60
    @12
    clt
    @18
    @59
    cB
    cmin
    oveq2
    breq1d
    rexbidv
    imbi12d
    supxrgere.y
    vtoclgf
    ax-mp
    syl2anc
    @58
    @61
    @52
    vy
    cA
    @58
    @61
    @52
    wi
    @26
    @58
    @61
    @52
    @58
    @61
    wa
    #
    @0
    @60
    @12
    clt
    @69
    @60
    @0
    @69
    cB
    @0
    wph
    cB
    cc
    wcel
    @7
    @56
    @61
    wph
    cB
    supxrgere.b
    recnd
    ad3antrrr
    @51
    @0
    cc
    wcel
    @56
    @61
    @51
    @0
    @65
    recnd
    ad2antrr
    nncand
    eqcomd
    @58
    @61
    simpr
    eqbrtrd
    ex
    adantr
    reximdva
    mpd
    syl2anc
    wph
    @53
    wn
    #
    @7
    @54
    wph
    @52
    wn
    #
    vy
    cA
    wral
    @70
    wph
    @71
    vy
    cA
    @43
    @46
    @71
    @48
    @43
    @12
    @0
    @30
    @43
    @33
    @32
    @47
    @34
    syl
    xrlenltd
    mpbid
    ralrimiva
    @52
    vy
    cA
    ralnex
    sylib
    ad2antrr
    condan
    syl2anc
    pm2.61dan
end
