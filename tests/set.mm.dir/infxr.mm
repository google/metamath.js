include "cxr.mm"
include "wcel.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cinf.mm"
include "wceq.mm"
include "wa.mm"
include "cr.mm"
include "r19.21bi.mm"
include "adantlr.mm"
include "cpnf.mm"
include "simplll.mm"
include "simpllr.mm"
include "simplr.mm"
include "cmnf.mm"
include "wne.mm"
include "mnfxr.mm"
include "a1i.mm"
include "ad2antrr.mm"
include "cle.mm"
include "mnfle.mm"
include "syl.mm"
include "simpr.mm"
include "xrlelttrd.mm"
include "xrgtned.mm"
include "xrnmnfpnf.mm"
include "w3a.mm"
include "c1.mm"
include "simpl.mm"
include "id.mm"
include "1re.mm"
include "mnflt.mm"
include "ax-mp.mm"
include "syl6eqbr.mm"
include "adantl.mm"
include "1red.mm"
include "breq2.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "sylc.mm"
include "nfv.mm"
include "nfan.mm"
include "sselda.mm"
include "ad4ant13.mm"
include "rexri.mm"
include "pnfxr.mm"
include "syl6eqel.mm"
include "ltpnf.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "xrlttrd.mm"
include "ex.mm"
include "reximdai.mm"
include "adantr.mm"
include "mpd.mm"
include "3adantl3.mm"
include "caddc.mm"
include "co.mm"
include "3ad2antl1.mm"
include "necon3bi.mm"
include "3adant1.mm"
include "xrltned.mm"
include "xrred.mm"
include "readdcld.mm"
include "jca.mm"
include "ltp1d.mm"
include "nf3an.mm"
include "rexrd.mm"
include "3adant3.mm"
include "ad3antrrr.mm"
include "ltpnfd.mm"
include "3ad2antl2.mm"
include "pm2.61dan.mm"
include "syl3anc.mm"
include "ralrimi.mm"
include "wtru.mm"
include "wor.mm"
include "xrltso.mm"
include "eqinf.mm"
include "trud.mm"

theorem infxr
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume infxr.x: |- F/ x ph
  assume infxr.y: |- F/ y ph
  assume infxr.a: |- ( ph -> A C_ RR* )
  assume infxr.b: |- ( ph -> B e. RR* )
  assume infxr.n: |- ( ph -> A. x e. A -. x < B )
  assume infxr.e: |- ( ph -> A. x e. RR ( B < x -> E. y e. A y < x ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  assert |- ( ph -> inf ( A , RR* , < ) = B )

  proof
    wph
    cB
    cxr
    wcel
    #
    vx
    cv
    #
    cB
    clt
    wbr
    wn
    vx
    cA
    wral
    #
    cB
    @1
    clt
    wbr
    #
    vy
    cv
    #
    @1
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    wi
    #
    vx
    cxr
    wral
    #
    cA
    cxr
    clt
    cinf
    cB
    wceq
    #
    infxr.b
    infxr.n
    wph
    @7
    vx
    cxr
    infxr.x
    wph
    @1
    cxr
    wcel
    #
    @7
    wph
    @10
    wa
    #
    @1
    cr
    wcel
    #
    @7
    wph
    @12
    @7
    @10
    wph
    @7
    vx
    cr
    infxr.e
    r19.21bi
    adantlr
    @11
    @12
    wn
    #
    wa
    #
    @3
    @6
    @14
    @3
    wa
    #
    wph
    @1
    cpnf
    wceq
    #
    @3
    @6
    wph
    @10
    @13
    @3
    simplll
    @15
    @1
    wph
    @10
    @13
    @3
    simpllr
    @11
    @13
    @3
    simplr
    @11
    @3
    @1
    cmnf
    wne
    @13
    @11
    @3
    wa
    #
    cmnf
    @1
    cmnf
    cxr
    wcel
    @17
    mnfxr
    a1i
    #
    wph
    @10
    @3
    simplr
    #
    @17
    cmnf
    cB
    @1
    @18
    wph
    @0
    @10
    @3
    infxr.b
    ad2antrr
    @19
    wph
    cmnf
    cB
    cle
    wbr
    #
    @10
    @3
    wph
    @0
    @20
    infxr.b
    cB
    mnfle
    syl
    ad2antrr
    @11
    @3
    simpr
    xrlelttrd
    xrgtned
    adantlr
    xrnmnfpnf
    @14
    @3
    simpr
    wph
    @16
    @3
    w3a
    #
    cB
    cmnf
    wceq
    #
    @6
    wph
    @16
    @22
    @6
    @3
    wph
    @16
    wa
    #
    @22
    wa
    @4
    c1
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    @6
    wph
    @22
    @25
    @16
    wph
    @22
    wa
    wph
    cB
    c1
    clt
    wbr
    #
    @25
    wph
    @22
    simpl
    @22
    @26
    wph
    @22
    cB
    cmnf
    c1
    clt
    @22
    id
    #
    c1
    cr
    wcel
    #
    cmnf
    c1
    clt
    wbr
    1re
    c1
    mnflt
    ax-mp
    syl6eqbr
    adantl
    wph
    @28
    @7
    vx
    cr
    wral
    #
    @26
    @25
    wi
    #
    wph
    1red
    infxr.e
    @7
    @30
    vx
    c1
    cr
    @1
    c1
    wceq
    #
    @3
    @26
    @6
    @25
    @1
    c1
    cB
    clt
    breq2
    @31
    @5
    @24
    vy
    cA
    @1
    c1
    @4
    clt
    breq2
    rexbidv
    imbi12d
    rspcva
    syl2anc
    sylc
    adantlr
    @23
    @25
    @6
    wi
    @22
    @23
    @24
    @5
    vy
    cA
    wph
    @16
    vy
    infxr.y
    @16
    vy
    nfv
    #
    nfan
    @23
    @4
    cA
    wcel
    #
    @24
    @5
    wi
    @23
    @33
    wa
    #
    @24
    @5
    @34
    @24
    wa
    #
    @4
    c1
    @1
    wph
    @33
    @4
    cxr
    wcel
    #
    @16
    @24
    wph
    cA
    cxr
    @4
    infxr.a
    sselda
    #
    ad4ant13
    c1
    cxr
    wcel
    @35
    c1
    1re
    rexri
    a1i
    @23
    @10
    @33
    @24
    @16
    @10
    wph
    @16
    @1
    cpnf
    cxr
    @16
    id
    #
    pnfxr
    syl6eqel
    adantl
    #
    ad2antrr
    @34
    @24
    simpr
    @23
    c1
    @1
    clt
    wbr
    #
    @33
    @24
    @16
    @40
    wph
    @16
    c1
    cpnf
    @1
    clt
    c1
    cpnf
    clt
    wbr
    #
    @16
    @28
    @41
    1re
    c1
    ltpnf
    ax-mp
    a1i
    @16
    @1
    cpnf
    @38
    eqcomd
    #
    breqtrd
    adantl
    ad2antrr
    xrlttrd
    ex
    ex
    reximdai
    adantr
    mpd
    3adantl3
    @21
    @22
    wn
    #
    wa
    #
    @4
    cB
    c1
    caddc
    co
    #
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    @6
    @44
    @45
    cr
    wcel
    #
    @29
    wa
    cB
    @45
    clt
    wbr
    #
    @47
    @44
    @48
    @29
    @44
    cB
    c1
    @44
    cB
    wph
    @16
    @43
    @0
    @3
    wph
    @0
    @43
    infxr.b
    adantr
    3ad2antl1
    #
    @43
    cB
    cmnf
    wne
    @21
    @22
    cB
    cmnf
    @27
    necon3bi
    adantl
    @44
    cB
    cpnf
    @50
    cpnf
    cxr
    wcel
    @44
    pnfxr
    a1i
    @21
    cB
    cpnf
    clt
    wbr
    #
    @43
    @16
    @3
    @51
    wph
    @16
    @3
    wa
    cB
    @1
    cpnf
    clt
    @16
    @3
    simpr
    @16
    @3
    simpl
    breqtrd
    3adant1
    adantr
    xrltned
    xrred
    #
    @28
    @44
    1re
    a1i
    readdcld
    #
    wph
    @16
    @43
    @29
    @3
    wph
    @29
    @43
    infxr.e
    adantr
    3ad2antl1
    jca
    @44
    cB
    @52
    ltp1d
    @7
    @49
    @47
    wi
    vx
    @45
    cr
    @1
    @45
    wceq
    #
    @3
    @49
    @6
    @47
    @1
    @45
    cB
    clt
    breq2
    @54
    @5
    @46
    vy
    cA
    @1
    @45
    @4
    clt
    breq2
    rexbidv
    imbi12d
    rspcva
    sylc
    @44
    @46
    @5
    vy
    cA
    @21
    @43
    vy
    wph
    @16
    @3
    vy
    infxr.y
    @32
    @3
    vy
    nfv
    nf3an
    @43
    vy
    nfv
    nfan
    @44
    @33
    @46
    @5
    wi
    @44
    @33
    wa
    #
    @46
    @5
    @55
    @46
    wa
    @4
    @45
    @1
    @21
    @33
    @36
    @43
    @46
    wph
    @16
    @33
    @36
    @3
    @37
    3ad2antl1
    ad4ant13
    @55
    @45
    cxr
    wcel
    @46
    @55
    @45
    @44
    @48
    @33
    @53
    adantr
    rexrd
    adantr
    @21
    @10
    @43
    @33
    @46
    wph
    @16
    @10
    @3
    @39
    3adant3
    ad3antrrr
    @55
    @46
    simpr
    @44
    @45
    @1
    clt
    wbr
    @33
    @46
    @44
    @45
    cpnf
    @1
    clt
    @44
    @45
    @53
    ltpnfd
    @16
    wph
    @43
    cpnf
    @1
    wceq
    #
    @3
    @16
    @56
    @43
    @42
    adantr
    3ad2antl2
    breqtrd
    ad2antrr
    xrlttrd
    ex
    ex
    reximdai
    mpd
    pm2.61dan
    syl3anc
    ex
    pm2.61dan
    ex
    ralrimi
    @0
    @2
    @8
    w3a
    @9
    wi
    wtru
    vx
    vy
    cxr
    cA
    cB
    clt
    cxr
    clt
    wor
    wtru
    xrltso
    a1i
    eqinf
    trud
    syl3anc
end
