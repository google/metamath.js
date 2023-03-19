include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cn.mm"
include "wral.mm"
include "wa.mm"
include "nfv.mm"
include "nfan.mm"
include "wcel.mm"
include "cxr.mm"
include "ad2antrr.mm"
include "cr.mm"
include "adantr.mm"
include "nnrecre.mm"
include "adantl.mm"
include "readdcld.mm"
include "rexrd.mm"
include "adantlr.mm"
include "rexr.mm"
include "syl.mm"
include "simplr.mm"
include "clt.mm"
include "crp.mm"
include "nnrp.mm"
include "rpreccl.mm"
include "ltaddrpd.mm"
include "xrlelttrd.mm"
include "xrltled.mm"
include "ex.mm"
include "ralrimi.mm"
include "wrex.mm"
include "rpgtrecnn.mm"
include "nfra1.mm"
include "wi.mm"
include "simpll.mm"
include "rspa.mm"
include "adantll.mm"
include "jca.mm"
include "simpr.mm"
include "ad4antr.mm"
include "rpre.mm"
include "ad5ant13.mm"
include "ad5ant14.mm"
include "simp-4r.mm"
include "ad2antlr.mm"
include "ltadd2dd.mm"
include "adantlllr.mm"
include "syl21anc.mm"
include "rexlimd.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "xralrple.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "impbid.mm"

theorem xrralrecnnle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vx: setvar x
  assume xrralrecnnle.n: |- F/ n ph
  assume xrralrecnnle.a: |- ( ph -> A e. RR* )
  assume xrralrecnnle.b: |- ( ph -> B e. RR )

  disjoint A n
  disjoint B n
  disjoint A x
  disjoint n x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> ( A <_ B <-> A. n e. NN A <_ ( B + ( 1 / n ) ) ) )

  proof
    wph
    cA
    cB
    cle
    wbr
    #
    cA
    cB
    c1
    vn
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
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
    xrralrecnnle.n
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
    cA
    @3
    wph
    cA
    cxr
    wcel
    #
    @0
    @7
    xrralrecnnle.a
    ad2antrr
    #
    wph
    @7
    @3
    cxr
    wcel
    #
    @0
    wph
    @7
    wa
    #
    @3
    @12
    cB
    @2
    wph
    cB
    cr
    wcel
    #
    @7
    xrralrecnnle.b
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
    readdcld
    rexrd
    #
    adantlr
    #
    @8
    cA
    cB
    @3
    @10
    wph
    cB
    cxr
    wcel
    #
    @0
    @7
    wph
    @13
    @19
    xrralrecnnle.b
    cB
    rexr
    syl
    ad2antrr
    @18
    wph
    @0
    @7
    simplr
    wph
    @7
    cB
    @3
    clt
    wbr
    @0
    @12
    cB
    @2
    @14
    @7
    @2
    crp
    wcel
    #
    wph
    @7
    @1
    crp
    wcel
    @20
    @1
    nnrp
    @1
    rpreccl
    syl
    adantl
    ltaddrpd
    adantlr
    xrlelttrd
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
    @0
    cA
    cB
    vx
    cv
    #
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
    @21
    @24
    vx
    crp
    @21
    @22
    crp
    wcel
    #
    wa
    #
    @2
    @22
    clt
    wbr
    #
    vn
    cn
    wrex
    #
    @24
    @26
    @29
    @21
    @22
    vn
    rpgtrecnn
    adantl
    @27
    @28
    @24
    vn
    cn
    @21
    @26
    vn
    wph
    @5
    vn
    xrralrecnnle.n
    @4
    vn
    cn
    nfra1
    nfan
    @26
    vn
    nfv
    nfan
    @24
    vn
    nfv
    @27
    @7
    @28
    @24
    wi
    #
    @27
    @7
    wa
    wph
    @4
    wa
    #
    @26
    @7
    @30
    @21
    @7
    @31
    @26
    @21
    @7
    wa
    wph
    @4
    wph
    @5
    @7
    simpll
    @5
    @7
    @4
    wph
    @4
    vn
    cn
    rspa
    adantll
    jca
    adantlr
    @21
    @26
    @7
    simplr
    @27
    @7
    simpr
    @31
    @26
    wa
    @7
    wa
    #
    @28
    @24
    @32
    @28
    wa
    #
    cA
    @23
    wph
    @9
    @4
    @26
    @7
    @28
    xrralrecnnle.a
    ad4antr
    #
    wph
    @26
    @23
    cxr
    wcel
    @4
    @7
    @28
    wph
    @26
    wa
    #
    @23
    @35
    cB
    @22
    wph
    @13
    @26
    xrralrecnnle.b
    adantr
    #
    @26
    @22
    cr
    wcel
    #
    wph
    @22
    rpre
    adantl
    #
    readdcld
    rexrd
    ad5ant13
    #
    @33
    cA
    @3
    @23
    @34
    wph
    @7
    @11
    @4
    @26
    @28
    @17
    ad5ant14
    @39
    wph
    @4
    @26
    @7
    @28
    simp-4r
    wph
    @26
    @7
    @28
    @3
    @23
    clt
    wbr
    @4
    @35
    @7
    wa
    #
    @28
    wa
    @2
    @22
    cB
    @7
    @15
    @35
    @28
    @16
    ad2antlr
    @35
    @37
    @7
    @28
    @38
    ad2antrr
    @35
    @13
    @7
    @28
    @36
    ad2antrr
    @40
    @28
    simpr
    ltadd2dd
    adantlllr
    xrlelttrd
    xrltled
    ex
    syl21anc
    ex
    rexlimd
    mpd
    ralrimiva
    wph
    @0
    @25
    wb
    #
    @5
    wph
    @9
    @13
    @41
    xrralrecnnle.a
    xrralrecnnle.b
    vx
    cA
    cB
    xralrple
    syl2anc
    adantr
    mpbird
    ex
    impbid
end
