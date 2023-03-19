include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cpnf.mm"
include "wceq.mm"
include "cv.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "wa.mm"
include "wcel.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "biimpi.mm"
include "syl.mm"
include "adantr.mm"
include "nfv.mm"
include "simpr.mm"
include "wss.mm"
include "sseldd.mm"
include "pnfge.mm"
include "adantlr.mm"
include "oveq1.mm"
include "adantl.mm"
include "cmnf.mm"
include "rpxrd.mm"
include "cr.mm"
include "rpred.mm"
include "renemnf.mm"
include "xaddpnf2.mm"
include "syl2anc.mm"
include "eqtr2d.mm"
include "breqtrd.mm"
include "jca.mm"
include "ex.mm"
include "eximd.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"
include "wn.mm"
include "simpl.mm"
include "wral.mm"
include "w3a.mm"
include "mnfxr.mm"
include "a1i.mm"
include "rexr.mm"
include "3ad2ant2.mm"
include "infxrcl.mm"
include "3ad2ant1.mm"
include "mnflt.mm"
include "simp3.mm"
include "wb.mm"
include "infxrgelb.mm"
include "3adant3.mm"
include "mpbird.mm"
include "xrltletrd.mm"
include "3exp.mm"
include "rexlimd.mm"
include "neqne.mm"
include "nepnfltpnf.mm"
include "xrrebnd.mm"
include "caddc.mm"
include "crp.mm"
include "ltaddrpd.mm"
include "rexadd.mm"
include "eqcomd.mm"
include "xaddcld.mm"
include "xrltnle.mm"
include "mpbid.mm"
include "mtbid.mm"
include "rexnal.mm"
include "wi.mm"
include "ad2antrr.mm"
include "xrltled.mm"
include "reximdva.mm"
include "pm2.61dan.mm"

theorem infrpge
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume infrpge.xph: |- F/ x ph
  assume infrpge.a: |- ( ph -> A C_ RR* )
  assume infrpge.an0: |- ( ph -> A =/= (/) )
  assume infrpge.bnd: |- ( ph -> E. x e. RR A. y e. A x <_ y )
  assume infrpge.b: |- ( ph -> B e. RR+ )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A z
  disjoint B z
  disjoint ph z
  assert |- ( ph -> E. z e. A z <_ ( inf ( A , RR* , < ) +e B ) )

  proof
    wph
    cA
    cxr
    clt
    cinf
    #
    cpnf
    wceq
    #
    vz
    cv
    #
    @0
    cB
    cxad
    co
    #
    cle
    wbr
    #
    vz
    cA
    wrex
    #
    wph
    @1
    wa
    #
    @2
    cA
    wcel
    #
    @4
    wa
    #
    vz
    wex
    #
    @5
    @6
    @7
    vz
    wex
    #
    @9
    wph
    @10
    @1
    wph
    cA
    c0
    wne
    #
    @10
    infrpge.an0
    @11
    @10
    vz
    cA
    n0
    biimpi
    syl
    adantr
    @6
    @7
    @8
    vz
    @6
    vz
    nfv
    @6
    @7
    @8
    @6
    @7
    wa
    #
    @7
    @4
    @6
    @7
    simpr
    @12
    @2
    cpnf
    @3
    cle
    wph
    @7
    @2
    cpnf
    cle
    wbr
    #
    @1
    wph
    @7
    wa
    #
    @2
    cxr
    wcel
    #
    @13
    @14
    cA
    cxr
    @2
    wph
    cA
    cxr
    wss
    #
    @7
    infrpge.a
    adantr
    wph
    @7
    simpr
    sseldd
    #
    @2
    pnfge
    syl
    adantlr
    @6
    cpnf
    @3
    wceq
    @7
    @6
    @3
    cpnf
    cB
    cxad
    co
    #
    cpnf
    @1
    @3
    @18
    wceq
    wph
    @0
    cpnf
    cB
    cxad
    oveq1
    adantl
    wph
    @18
    cpnf
    wceq
    #
    @1
    wph
    cB
    cxr
    wcel
    cB
    cmnf
    wne
    #
    @19
    wph
    cB
    infrpge.b
    rpxrd
    #
    wph
    cB
    cr
    wcel
    #
    @20
    wph
    cB
    infrpge.b
    rpred
    #
    cB
    renemnf
    syl
    cB
    xaddpnf2
    syl2anc
    adantr
    eqtr2d
    adantr
    breqtrd
    jca
    ex
    eximd
    mpd
    @4
    vz
    cA
    df-rex
    sylibr
    wph
    @1
    wn
    #
    wa
    #
    @3
    @2
    cle
    wbr
    #
    wn
    #
    vz
    cA
    wrex
    #
    @5
    @25
    wph
    @3
    @0
    cle
    wbr
    #
    wn
    #
    @28
    wph
    @24
    simpl
    #
    @25
    wph
    @0
    cr
    wcel
    #
    @30
    @31
    @25
    @32
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
    @25
    @33
    @34
    wph
    @33
    @24
    wph
    vx
    cv
    #
    vy
    cv
    cle
    wbr
    vy
    cA
    wral
    #
    vx
    cr
    wrex
    @33
    infrpge.bnd
    wph
    @37
    @33
    vx
    cr
    infrpge.xph
    @33
    vx
    nfv
    wph
    @36
    cr
    wcel
    #
    @37
    @33
    wph
    @38
    @37
    w3a
    #
    cmnf
    @36
    @0
    cmnf
    cxr
    wcel
    @39
    mnfxr
    a1i
    @38
    wph
    @36
    cxr
    wcel
    #
    @37
    @36
    rexr
    #
    3ad2ant2
    wph
    @38
    @0
    cxr
    wcel
    #
    @37
    wph
    @16
    @42
    infrpge.a
    cA
    infxrcl
    syl
    #
    3ad2ant1
    @38
    wph
    cmnf
    @36
    clt
    wbr
    @37
    @36
    mnflt
    3ad2ant2
    @39
    @36
    @0
    cle
    wbr
    #
    @37
    wph
    @38
    @37
    simp3
    wph
    @38
    @44
    @37
    wb
    #
    @37
    wph
    @38
    wa
    @16
    @40
    @45
    wph
    @16
    @38
    infrpge.a
    adantr
    @38
    @40
    wph
    @41
    adantl
    vy
    cA
    @36
    infxrgelb
    syl2anc
    3adant3
    mpbird
    xrltletrd
    3exp
    rexlimd
    mpd
    adantr
    @25
    @0
    @24
    @0
    cpnf
    wne
    wph
    @0
    cpnf
    neqne
    adantl
    wph
    @42
    @24
    @43
    adantr
    nepnfltpnf
    jca
    wph
    @32
    @35
    wb
    #
    @24
    wph
    @42
    @46
    @43
    @0
    xrrebnd
    syl
    adantr
    mpbird
    wph
    @32
    wa
    #
    @0
    @3
    clt
    wbr
    #
    @30
    @47
    @0
    @0
    cB
    caddc
    co
    #
    @3
    clt
    @47
    @0
    cB
    wph
    @32
    simpr
    #
    wph
    cB
    crp
    wcel
    @32
    infrpge.b
    adantr
    ltaddrpd
    @47
    @3
    @49
    @47
    @32
    @22
    @3
    @49
    wceq
    @50
    wph
    @22
    @32
    @23
    adantr
    @0
    cB
    rexadd
    syl2anc
    eqcomd
    breqtrd
    @47
    @42
    @3
    cxr
    wcel
    #
    @48
    @30
    wb
    wph
    @42
    @32
    @43
    adantr
    wph
    @51
    @32
    wph
    @0
    cB
    @43
    @21
    xaddcld
    #
    adantr
    @0
    @3
    xrltnle
    syl2anc
    mpbid
    syl2anc
    wph
    @30
    wa
    #
    @26
    vz
    cA
    wral
    #
    wn
    @28
    @53
    @29
    @54
    wph
    @30
    simpr
    @53
    wph
    @29
    @54
    wb
    #
    wph
    @30
    simpl
    wph
    @16
    @51
    @55
    infrpge.a
    @52
    vz
    cA
    @3
    infxrgelb
    syl2anc
    syl
    mtbid
    @26
    vz
    cA
    rexnal
    sylibr
    syl2anc
    @25
    @27
    @4
    vz
    cA
    wph
    @7
    @27
    @4
    wi
    @24
    @14
    @27
    @4
    @14
    @27
    wa
    #
    @2
    @3
    @14
    @15
    @27
    @17
    adantr
    #
    wph
    @51
    @7
    @27
    @52
    ad2antrr
    #
    @56
    @2
    @3
    clt
    wbr
    #
    @27
    @14
    @27
    simpr
    @56
    @15
    @51
    @59
    @27
    wb
    @57
    @58
    @2
    @3
    xrltnle
    syl2anc
    mpbird
    xrltled
    ex
    adantlr
    reximdva
    mpd
    pm2.61dan
end
