include "cpnf.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cxr.mm"
include "wcel.mm"
include "pnfge.mm"
include "syl.mm"
include "adantr.mm"
include "id.mm"
include "eqcomd.mm"
include "adantl.mm"
include "breqtrd.mm"
include "wn.mm"
include "wne.mm"
include "simpl.mm"
include "neqne.mm"
include "cmnf.mm"
include "simpr.mm"
include "mnfle.mm"
include "eqbrtrd.mm"
include "adantlr.mm"
include "cr.mm"
include "simpll.mm"
include "wo.mm"
include "jca.mm"
include "xrnepnf.mm"
include "sylib.mm"
include "pm2.53.mm"
include "sylc.mm"
include "c1.mm"
include "cxad.mm"
include "co.mm"
include "crp.mm"
include "1rp.mm"
include "a1i.mm"
include "cv.mm"
include "wi.mm"
include "1re.mm"
include "elexi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "vtocl.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "clt.mm"
include "oveq1.mm"
include "rexri.mm"
include "ltpnf.mm"
include "ax-mp.mm"
include "ltneii.mm"
include "xaddmnf2.mm"
include "mp2an.mm"
include "eqtr2d.mm"
include "nemnftgtmnft.mm"
include "wb.mm"
include "xaddcld.mm"
include "xrltnle.mm"
include "mpbid.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "ad4ant13.mm"
include "neneqd.mm"
include "condan.mm"
include "caddc.mm"
include "wral.mm"
include "rpre.mm"
include "rexadd.mm"
include "adantll.mm"
include "ralrimiva.mm"
include "xralrple.mm"
include "mpbird.mm"
include "pm2.61dan.mm"

theorem xrlexaddrp
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume xrlexaddrp.1: |- ( ph -> A e. RR* )
  assume xrlexaddrp.2: |- ( ph -> B e. RR* )
  assume xrlexaddrp.3: |- ( ( ph /\ x e. RR+ ) -> A <_ ( B +e x ) )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> A <_ B )

  proof
    wph
    cB
    cpnf
    wceq
    #
    cA
    cB
    cle
    wbr
    #
    wph
    @0
    wa
    cA
    cpnf
    cB
    cle
    wph
    cA
    cpnf
    cle
    wbr
    #
    @0
    wph
    cA
    cxr
    wcel
    #
    @2
    xrlexaddrp.1
    cA
    pnfge
    syl
    adantr
    @0
    cpnf
    cB
    wceq
    wph
    @0
    cB
    cpnf
    @0
    id
    eqcomd
    adantl
    breqtrd
    wph
    @0
    wn
    #
    wa
    wph
    cB
    cpnf
    wne
    #
    @1
    wph
    @4
    simpl
    @4
    @5
    wph
    cB
    cpnf
    neqne
    adantl
    wph
    @5
    wa
    #
    cA
    cmnf
    wceq
    #
    @1
    wph
    @7
    @1
    @5
    wph
    @7
    wa
    cA
    cmnf
    cB
    cle
    wph
    @7
    simpr
    wph
    cmnf
    cB
    cle
    wbr
    #
    @7
    wph
    cB
    cxr
    wcel
    #
    @8
    xrlexaddrp.2
    cB
    mnfle
    syl
    adantr
    eqbrtrd
    adantlr
    @6
    @7
    wn
    #
    wa
    @6
    cA
    cmnf
    wne
    #
    @1
    @6
    @10
    simpl
    @10
    @11
    @6
    cA
    cmnf
    neqne
    adantl
    @6
    @11
    wa
    #
    wph
    cB
    cr
    wcel
    #
    @1
    wph
    @5
    @11
    simpll
    @12
    @13
    cB
    cmnf
    wceq
    #
    @6
    @13
    wn
    #
    @14
    @11
    @6
    @15
    wa
    @13
    @14
    wo
    #
    @15
    @14
    @6
    @16
    @15
    @6
    @9
    @5
    wa
    @16
    @6
    @9
    @5
    wph
    @9
    @5
    xrlexaddrp.2
    adantr
    wph
    @5
    simpr
    jca
    cB
    xrnepnf
    sylib
    adantr
    @6
    @15
    simpr
    @13
    @14
    pm2.53
    sylc
    adantlr
    @12
    @15
    wa
    cB
    cmnf
    wph
    @11
    cB
    cmnf
    wne
    @5
    @15
    wph
    @11
    wa
    #
    cB
    cmnf
    @17
    @14
    cA
    cB
    c1
    cxad
    co
    #
    cle
    wbr
    #
    wph
    @19
    @11
    @14
    wph
    wph
    c1
    crp
    wcel
    #
    @19
    wph
    id
    @20
    wph
    1rp
    a1i
    wph
    vx
    cv
    #
    crp
    wcel
    #
    wa
    #
    cA
    cB
    @21
    cxad
    co
    #
    cle
    wbr
    #
    wi
    wph
    @20
    wa
    #
    @19
    wi
    vx
    c1
    c1
    cr
    1re
    elexi
    @21
    c1
    wceq
    #
    @23
    @26
    @25
    @19
    @27
    @22
    @20
    wph
    @21
    c1
    crp
    eleq1
    anbi2d
    @27
    @24
    @18
    cA
    cle
    @21
    c1
    cB
    cxad
    oveq2
    breq2d
    imbi12d
    xrlexaddrp.3
    vtocl
    syl2anc
    ad2antrr
    @17
    @14
    wa
    #
    @18
    cA
    clt
    wbr
    #
    @19
    wn
    #
    @28
    @18
    cmnf
    cA
    clt
    @28
    cmnf
    @18
    @14
    cmnf
    @18
    wceq
    @17
    @14
    @18
    cmnf
    c1
    cxad
    co
    #
    cmnf
    cB
    cmnf
    c1
    cxad
    oveq1
    @31
    cmnf
    wceq
    #
    @14
    c1
    cxr
    wcel
    #
    c1
    cpnf
    wne
    @32
    c1
    1re
    rexri
    #
    c1
    cpnf
    1re
    c1
    cr
    wcel
    c1
    cpnf
    clt
    wbr
    1re
    c1
    ltpnf
    ax-mp
    ltneii
    c1
    xaddmnf2
    mp2an
    a1i
    eqtr2d
    adantl
    eqcomd
    @17
    cmnf
    cA
    clt
    wbr
    #
    @14
    @17
    @3
    @11
    @35
    wph
    @3
    @11
    xrlexaddrp.1
    adantr
    wph
    @11
    simpr
    cA
    nemnftgtmnft
    syl2anc
    adantr
    eqbrtrd
    @28
    @18
    cxr
    wcel
    @3
    @29
    @30
    wb
    @28
    cB
    c1
    wph
    @9
    @11
    @14
    xrlexaddrp.2
    ad2antrr
    @33
    @28
    @34
    a1i
    xaddcld
    wph
    @3
    @11
    @14
    xrlexaddrp.1
    ad2antrr
    @18
    cA
    xrltnle
    syl2anc
    mpbid
    pm2.65da
    neqned
    ad4ant13
    neneqd
    condan
    wph
    @13
    wa
    #
    @1
    cA
    cB
    @21
    caddc
    co
    #
    cle
    wbr
    #
    vx
    crp
    wral
    #
    @36
    @38
    vx
    crp
    @36
    @22
    wa
    cA
    @24
    @37
    cle
    wph
    @22
    @25
    @13
    xrlexaddrp.3
    adantlr
    @13
    @22
    @24
    @37
    wceq
    #
    wph
    @13
    @22
    wa
    @13
    @21
    cr
    wcel
    #
    @40
    @13
    @22
    simpl
    @22
    @41
    @13
    @21
    rpre
    adantl
    cB
    @21
    rexadd
    syl2anc
    adantll
    breqtrd
    ralrimiva
    @36
    @3
    @13
    @1
    @39
    wb
    wph
    @3
    @13
    xrlexaddrp.1
    adantr
    wph
    @13
    simpr
    vx
    cA
    cB
    xralrple
    syl2anc
    mpbird
    syl2anc
    syl2anc
    pm2.61dan
    syl2anc
    pm2.61dan
end
