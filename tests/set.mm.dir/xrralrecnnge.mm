include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "cn.mm"
include "wral.mm"
include "wa.mm"
include "nfv.mm"
include "nfan.mm"
include "wcel.mm"
include "cxr.mm"
include "cr.mm"
include "adantr.mm"
include "nnrecre.mm"
include "adantl.mm"
include "resubcld.mm"
include "rexrd.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "clt.mm"
include "crp.mm"
include "nnrp.mm"
include "rpreccld.mm"
include "ltsubrpd.mm"
include "simplr.mm"
include "xrltletrd.mm"
include "xrltled.mm"
include "ex.mm"
include "ralrimi.mm"
include "cpnf.mm"
include "wceq.mm"
include "pnfxr.mm"
include "a1i.mm"
include "ltpnfd.mm"
include "id.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "wn.mm"
include "cmnf.mm"
include "wne.mm"
include "1nn.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "breq1d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "simpr.mm"
include "adantll.mm"
include "1red.mm"
include "cc0.mm"
include "ax-1ne0.mm"
include "redivcld.mm"
include "mnfltd.mm"
include "mnfxr.mm"
include "xrltnled.mm"
include "mpbid.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "neqne.mm"
include "xrred.mm"
include "caddc.mm"
include "xrralrecnnle.mm"
include "lesubaddd.mm"
include "bicomd.mm"
include "ralbida.mm"
include "bitr2d.mm"
include "biimpd.mm"
include "imp.mm"
include "an32s.mm"
include "syldan.mm"
include "pm2.61dan.mm"
include "impbid.mm"

theorem xrralrecnnge
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vn: setvar n
  assume xrralrecnnge.n: |- F/ n ph
  assume xrralrecnnge.a: |- ( ph -> A e. RR )
  assume xrralrecnnge.b: |- ( ph -> B e. RR* )

  disjoint A n
  disjoint B n
  assert |- ( ph -> ( A <_ B <-> A. n e. NN ( A - ( 1 / n ) ) <_ B ) )

  proof
    wph
    cA
    cB
    cle
    wbr
    #
    cA
    c1
    vn
    cv
    #
    cdiv
    co
    #
    cmin
    co
    #
    cB
    cle
    wbr
    #
    vn
    cn
    wral
    #
    wph
    @0
    @5
    wph
    @0
    wa
    #
    @4
    vn
    cn
    wph
    @0
    vn
    xrralrecnnge.n
    @0
    vn
    nfv
    nfan
    @6
    @1
    cn
    wcel
    #
    @4
    @6
    @7
    wa
    #
    @3
    cB
    wph
    @7
    @3
    cxr
    wcel
    @0
    wph
    @7
    wa
    #
    @3
    @9
    cA
    @2
    wph
    cA
    cr
    wcel
    #
    @7
    xrralrecnnge.a
    adantr
    #
    @7
    @2
    cr
    wcel
    #
    wph
    @1
    nnrecre
    #
    adantl
    resubcld
    rexrd
    adantlr
    #
    wph
    cB
    cxr
    wcel
    #
    @0
    @7
    xrralrecnnge.b
    ad2antrr
    #
    @8
    @3
    cA
    cB
    @14
    wph
    cA
    cxr
    wcel
    #
    @0
    @7
    wph
    cA
    xrralrecnnge.a
    rexrd
    #
    ad2antrr
    @16
    wph
    @7
    @3
    cA
    clt
    wbr
    @0
    @9
    cA
    @2
    @11
    @7
    @2
    crp
    wcel
    wph
    @7
    @1
    @1
    nnrp
    rpreccld
    adantl
    ltsubrpd
    adantlr
    wph
    @0
    @7
    simplr
    xrltletrd
    xrltled
    ex
    ralrimi
    ex
    wph
    @5
    @0
    wph
    @5
    wa
    #
    cB
    cpnf
    wceq
    #
    @0
    @19
    @20
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
    @5
    @20
    wph
    cA
    cpnf
    @18
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    wph
    cA
    xrralrecnnge.a
    ltpnfd
    xrltled
    ad2antrr
    @20
    cpnf
    cB
    wceq
    @19
    @20
    cB
    cpnf
    @20
    id
    eqcomd
    adantl
    breqtrd
    @19
    @20
    wn
    #
    cB
    cr
    wcel
    #
    @0
    @19
    @21
    wa
    cB
    wph
    @15
    @5
    @21
    xrralrecnnge.b
    ad2antrr
    @19
    cB
    cmnf
    wne
    @21
    @19
    cB
    cmnf
    @19
    cB
    cmnf
    wceq
    #
    cA
    c1
    c1
    cdiv
    co
    #
    cmin
    co
    #
    cmnf
    cle
    wbr
    #
    @5
    @23
    @26
    wph
    @5
    @23
    wa
    @25
    cB
    cmnf
    cle
    @5
    @25
    cB
    cle
    wbr
    #
    @23
    @5
    c1
    cn
    wcel
    #
    @5
    @27
    @28
    @5
    1nn
    a1i
    @5
    id
    @4
    @27
    vn
    c1
    cn
    @1
    c1
    wceq
    #
    @3
    @25
    cB
    cle
    @29
    @2
    @24
    cA
    cmin
    @1
    c1
    c1
    cdiv
    oveq2
    oveq2d
    breq1d
    rspcva
    syl2anc
    adantr
    @5
    @23
    simpr
    breqtrd
    adantll
    wph
    @26
    wn
    #
    @5
    @23
    wph
    cmnf
    @25
    clt
    wbr
    @30
    wph
    @25
    wph
    cA
    @24
    xrralrecnnge.a
    wph
    c1
    c1
    wph
    1red
    #
    @31
    c1
    cc0
    wne
    wph
    ax-1ne0
    a1i
    redivcld
    resubcld
    #
    mnfltd
    wph
    cmnf
    @25
    cmnf
    cxr
    wcel
    wph
    mnfxr
    a1i
    wph
    @25
    @32
    rexrd
    xrltnled
    mpbid
    ad2antrr
    pm2.65da
    neqned
    adantr
    @21
    cB
    cpnf
    wne
    @19
    cB
    cpnf
    neqne
    adantl
    xrred
    wph
    @22
    @5
    @0
    wph
    @22
    wa
    #
    @5
    @0
    @33
    @5
    @0
    @33
    @0
    cA
    cB
    @2
    caddc
    co
    cle
    wbr
    #
    vn
    cn
    wral
    @5
    @33
    cA
    cB
    vn
    wph
    @22
    vn
    xrralrecnnge.n
    @22
    vn
    nfv
    nfan
    #
    wph
    @17
    @22
    @18
    adantr
    wph
    @22
    simpr
    #
    xrralrecnnle
    @33
    @34
    @4
    vn
    cn
    @35
    @33
    @7
    wa
    #
    @4
    @34
    @37
    cA
    @2
    cB
    wph
    @7
    @10
    @22
    @11
    adantlr
    @7
    @12
    @33
    @13
    adantl
    @33
    @22
    @7
    @36
    adantr
    lesubaddd
    bicomd
    ralbida
    bitr2d
    biimpd
    imp
    an32s
    syldan
    pm2.61dan
    ex
    impbid
end
