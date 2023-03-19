include "cpnf.mm"
include "wcel.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "pnfge.mm"
include "syl.mm"
include "adantr.mm"
include "wss.mm"
include "wceq.mm"
include "simpr.mm"
include "supxrpnf.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "wn.mm"
include "cmnf.mm"
include "supxrcl.mm"
include "mnfle.mm"
include "eqbrtrd.mm"
include "adantlr.mm"
include "wne.mm"
include "simpl.mm"
include "neqne.mm"
include "adantl.mm"
include "nfv.mm"
include "cv.mm"
include "crp.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cxad.mm"
include "wrex.mm"
include "rphalfcl.mm"
include "cvv.mm"
include "wi.mm"
include "ovex.mm"
include "nfcv.mm"
include "nfan.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "breq2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "vtoclgf.mm"
include "ax-mp.mm"
include "w3a.mm"
include "cr.mm"
include "neneq.mm"
include "wb.mm"
include "ngtmnft.mm"
include "mtbid.mm"
include "notnotrd.mm"
include "ad4ant13.mm"
include "3ad2ant1.mm"
include "caddc.mm"
include "mnfxr.mm"
include "a1i.mm"
include "simpl3.mm"
include "sselda.mm"
include "mpbird.mm"
include "oveq1d.mm"
include "adantllr.mm"
include "rpxrd.mm"
include "rpred.mm"
include "renepnf.mm"
include "xaddmnf2.mm"
include "ad2antrr.mm"
include "eqtrd.mm"
include "adantlllr.mm"
include "3adantl3.mm"
include "ad3antrrr.mm"
include "3ad2antl1.mm"
include "xrletrid.mm"
include "simpllr.mm"
include "neneqd.mm"
include "condan.mm"
include "nltpnft.mm"
include "eqeltrd.mm"
include "3adantl2.mm"
include "simpl2.mm"
include "ad5ant125.mm"
include "3adant3.mm"
include "jca.mm"
include "ad5ant15.mm"
include "xrrebnd.mm"
include "rexadd.mm"
include "readdcld.mm"
include "rexrd.mm"
include "pnfxr.mm"
include "simp3.mm"
include "ltpnfd.mm"
include "xrlelttrd.mm"
include "rpre.mm"
include "rphalflt.mm"
include "ltadd2dd.mm"
include "breq12d.mm"
include "lelttrd.mm"
include "3exp.mm"
include "reximdai.mm"
include "mpd.mm"
include "supxrgelem.mm"
include "pm2.61dan.mm"

theorem supxrge
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  assume supxrge.xph: |- F/ x ph
  assume supxrge.a: |- ( ph -> A C_ RR* )
  assume supxrge.b: |- ( ph -> B e. RR* )
  assume supxrge.y: |- ( ( ph /\ x e. RR+ ) -> E. y e. A B <_ ( y +e x ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ph y
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint ph w
  assert |- ( ph -> B <_ sup ( A , RR* , < ) )

  proof
    wph
    cpnf
    cA
    wcel
    #
    cB
    cA
    cxr
    clt
    csup
    #
    cle
    wbr
    #
    wph
    @0
    wa
    #
    cB
    cpnf
    @1
    cle
    wph
    cB
    cpnf
    cle
    wbr
    #
    @0
    wph
    cB
    cxr
    wcel
    #
    @4
    supxrge.b
    cB
    pnfge
    syl
    adantr
    @3
    @1
    cpnf
    @3
    cA
    cxr
    wss
    #
    @0
    @1
    cpnf
    wceq
    wph
    @6
    @0
    supxrge.a
    adantr
    wph
    @0
    simpr
    cA
    supxrpnf
    syl2anc
    eqcomd
    breqtrd
    wph
    @0
    wn
    #
    wa
    #
    cB
    cmnf
    wceq
    #
    @2
    wph
    @9
    @2
    @7
    wph
    @9
    wa
    cB
    cmnf
    @1
    cle
    wph
    @9
    simpr
    wph
    cmnf
    @1
    cle
    wbr
    #
    @9
    wph
    @1
    cxr
    wcel
    #
    @10
    wph
    @6
    @11
    supxrge.a
    cA
    supxrcl
    syl
    @1
    mnfle
    syl
    adantr
    eqbrtrd
    adantlr
    @8
    @9
    wn
    #
    wa
    @8
    cB
    cmnf
    wne
    #
    @2
    @8
    @12
    simpl
    @12
    @13
    @8
    cB
    cmnf
    neqne
    adantl
    @8
    @13
    wa
    #
    vw
    vy
    cA
    cB
    @14
    vw
    nfv
    @8
    @6
    @13
    wph
    @6
    @7
    supxrge.a
    adantr
    adantr
    @8
    @5
    @13
    wph
    @5
    @7
    supxrge.b
    adantr
    adantr
    #
    @14
    vw
    cv
    #
    crp
    wcel
    #
    wa
    #
    cB
    vy
    cv
    #
    @16
    c2
    cdiv
    co
    #
    cxad
    co
    #
    cle
    wbr
    #
    vy
    cA
    wrex
    #
    cB
    @19
    @16
    cxad
    co
    #
    clt
    wbr
    #
    vy
    cA
    wrex
    @8
    @17
    @23
    @13
    wph
    @17
    @23
    @7
    wph
    @17
    wa
    #
    wph
    @20
    crp
    wcel
    #
    @23
    wph
    @17
    simpl
    @17
    @27
    wph
    @16
    rphalfcl
    #
    adantl
    @20
    cvv
    wcel
    wph
    @27
    wa
    #
    @23
    wi
    #
    @16
    c2
    cdiv
    ovex
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
    @19
    @31
    cxad
    co
    #
    cle
    wbr
    #
    vy
    cA
    wrex
    #
    wi
    @30
    vx
    @20
    cvv
    vx
    @20
    nfcv
    @29
    @23
    vx
    wph
    @27
    vx
    supxrge.xph
    @27
    vx
    nfv
    nfan
    @23
    vx
    nfv
    nfim
    @31
    @20
    wceq
    #
    @33
    @29
    @36
    @23
    @37
    @32
    @27
    wph
    @31
    @20
    crp
    eleq1
    anbi2d
    @37
    @35
    @22
    vy
    cA
    @37
    @34
    @21
    cB
    cle
    @31
    @20
    @19
    cxad
    oveq2
    breq2d
    rexbidv
    imbi12d
    supxrge.y
    vtoclgf
    ax-mp
    syl2anc
    adantlr
    adantlr
    @18
    @22
    @25
    vy
    cA
    @18
    vy
    nfv
    @18
    @19
    cA
    wcel
    #
    @22
    @25
    @18
    @38
    @22
    w3a
    #
    cB
    @21
    @24
    @39
    cB
    cr
    wcel
    #
    cmnf
    cB
    clt
    wbr
    #
    cB
    cpnf
    clt
    wbr
    #
    wa
    #
    @39
    @41
    @42
    @18
    @38
    @41
    @22
    wph
    @13
    @41
    @7
    @17
    wph
    @13
    wa
    #
    @41
    @44
    @9
    @41
    wn
    #
    @13
    @12
    wph
    cB
    cmnf
    neneq
    adantl
    @44
    @5
    @9
    @45
    wb
    wph
    @5
    @13
    supxrge.b
    adantr
    cB
    ngtmnft
    syl
    mtbid
    notnotrd
    ad4ant13
    3ad2ant1
    @39
    cB
    @21
    cpnf
    @18
    @38
    @5
    @22
    @14
    @5
    @17
    @15
    adantr
    3ad2ant1
    #
    @39
    @21
    @39
    @21
    @19
    @20
    caddc
    co
    #
    cr
    @39
    @19
    cr
    wcel
    #
    @20
    cr
    wcel
    #
    @21
    @47
    wceq
    @39
    @48
    cmnf
    @19
    clt
    wbr
    #
    @19
    cpnf
    clt
    wbr
    #
    wa
    #
    @39
    @50
    @51
    @39
    @50
    @9
    @39
    @50
    wn
    #
    wa
    #
    cB
    cmnf
    @39
    @5
    @53
    @46
    adantr
    cmnf
    cxr
    wcel
    @54
    mnfxr
    a1i
    @54
    cB
    @21
    cmnf
    cle
    @18
    @38
    @22
    @53
    simpl3
    @18
    @38
    @53
    @21
    cmnf
    wceq
    #
    @22
    @8
    @17
    @38
    @53
    @55
    @13
    wph
    @17
    @38
    @53
    @55
    @7
    @26
    @38
    wa
    @53
    wa
    @21
    cmnf
    @20
    cxad
    co
    #
    cmnf
    wph
    @38
    @53
    @21
    @56
    wceq
    @17
    wph
    @38
    wa
    #
    @53
    wa
    #
    @19
    cmnf
    @20
    cxad
    @58
    @19
    cmnf
    wceq
    #
    @53
    @57
    @53
    simpr
    @58
    @19
    cxr
    wcel
    #
    @59
    @53
    wb
    @57
    @60
    @53
    wph
    cA
    cxr
    @19
    supxrge.a
    sselda
    #
    adantr
    @19
    ngtmnft
    syl
    mpbird
    oveq1d
    adantllr
    @26
    @56
    cmnf
    wceq
    #
    @38
    @53
    @17
    @62
    wph
    @17
    @20
    cxr
    wcel
    @20
    cpnf
    wne
    #
    @62
    @17
    @20
    @28
    rpxrd
    @17
    @49
    @63
    @17
    @20
    @28
    rpred
    #
    @20
    renepnf
    syl
    @20
    xaddmnf2
    syl2anc
    adantl
    ad2antrr
    eqtrd
    adantlllr
    adantlllr
    3adantl3
    breqtrd
    @18
    @38
    @53
    cmnf
    cB
    cle
    wbr
    #
    @22
    @8
    @65
    @13
    @17
    @53
    wph
    @65
    @7
    wph
    @5
    @65
    supxrge.b
    cB
    mnfle
    syl
    adantr
    ad3antrrr
    3ad2antl1
    xrletrid
    @54
    cB
    cmnf
    @18
    @38
    @53
    @13
    @22
    @8
    @13
    @17
    @53
    simpllr
    3ad2antl1
    neneqd
    condan
    @18
    @38
    @51
    @22
    wph
    @7
    @38
    @51
    @13
    @17
    wph
    @7
    @38
    w3a
    @51
    @0
    wph
    @38
    @51
    wn
    #
    @0
    @7
    @57
    @66
    wa
    #
    cpnf
    @19
    cA
    @67
    @19
    cpnf
    @67
    @19
    cpnf
    wceq
    #
    @66
    @57
    @66
    simpr
    @67
    @60
    @68
    @66
    wb
    @57
    @60
    @66
    @61
    adantr
    @19
    nltpnft
    syl
    mpbird
    eqcomd
    @57
    @38
    @66
    wph
    @38
    simpr
    adantr
    eqeltrd
    3adantl2
    wph
    @7
    @38
    @66
    simpl2
    condan
    ad5ant125
    3adant3
    jca
    @39
    @60
    @48
    @52
    wb
    @18
    @38
    @60
    @22
    wph
    @38
    @60
    @7
    @13
    @17
    @61
    ad5ant15
    3adant3
    @19
    xrrebnd
    syl
    mpbird
    #
    @18
    @38
    @49
    @22
    @17
    @49
    @14
    @64
    adantl
    3ad2ant1
    #
    @19
    @20
    rexadd
    syl2anc
    #
    @39
    @19
    @20
    @69
    @70
    readdcld
    eqeltrd
    #
    rexrd
    cpnf
    cxr
    wcel
    @39
    pnfxr
    a1i
    @18
    @38
    @22
    simp3
    #
    @39
    @21
    @72
    ltpnfd
    xrlelttrd
    jca
    @39
    @5
    @40
    @43
    wb
    @46
    cB
    xrrebnd
    syl
    mpbird
    @72
    @39
    @24
    @19
    @16
    caddc
    co
    #
    cr
    @39
    @48
    @16
    cr
    wcel
    #
    @24
    @74
    wceq
    @69
    @18
    @38
    @75
    @22
    @17
    @75
    @14
    @16
    rpre
    adantl
    3ad2ant1
    #
    @19
    @16
    rexadd
    syl2anc
    #
    @39
    @19
    @16
    @69
    @76
    readdcld
    eqeltrd
    @73
    @39
    @21
    @24
    clt
    wbr
    @47
    @74
    clt
    wbr
    @39
    @20
    @16
    @19
    @70
    @76
    @69
    @18
    @38
    @20
    @16
    clt
    wbr
    #
    @22
    @17
    @78
    @14
    @16
    rphalflt
    adantl
    3ad2ant1
    ltadd2dd
    @39
    @21
    @47
    @24
    @74
    clt
    @71
    @77
    breq12d
    mpbird
    lelttrd
    3exp
    reximdai
    mpd
    supxrgelem
    syl2anc
    pm2.61dan
    pm2.61dan
end
