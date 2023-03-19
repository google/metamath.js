include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "crp.mm"
include "wral.mm"
include "wa.mm"
include "wcel.mm"
include "cxr.mm"
include "ad2antrr.mm"
include "rexrd.mm"
include "cr.mm"
include "rpre.mm"
include "adantl.mm"
include "remulcld.mm"
include "readdcld.mm"
include "simplr.mm"
include "cc0.mm"
include "adantr.mm"
include "rpge0.mm"
include "mulge0d.mm"
include "addge01d.mm"
include "mpbid.mm"
include "adantlr.mm"
include "xrletrd.mm"
include "ralrimiva.mm"
include "ex.mm"
include "wceq.mm"
include "c1.mm"
include "1rp.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "breq2d.mm"
include "rspcva.mm"
include "mpan.mm"
include "ad2antlr.mm"
include "oveq1.mm"
include "0cn.mm"
include "mulid1i.mm"
include "a1i.mm"
include "eqtrd.mm"
include "cc.mm"
include "recnd.mm"
include "addid1d.mm"
include "breqtrd.mm"
include "wn.mm"
include "wne.mm"
include "neqne.mm"
include "0red.mm"
include "simpr.mm"
include "leneltd.mm"
include "elrpd.mm"
include "syldan.mm"
include "cdiv.mm"
include "simpl.mm"
include "rpdivcld.mm"
include "adantll.mm"
include "simpll.mm"
include "syl2anc.mm"
include "adantlll.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divcan2d.mm"
include "wb.mm"
include "xralrple.mm"
include "mpbird.mm"
include "pm2.61dan.mm"
include "impbid.mm"

theorem xralrple3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume xralrple3.a: |- ( ph -> A e. RR* )
  assume xralrple3.b: |- ( ph -> B e. RR )
  assume xralrple3.c: |- ( ph -> C e. RR )
  assume xralrple3.g: |- ( ph -> 0 <_ C )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ph x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  disjoint ph y
  assert |- ( ph -> ( A <_ B <-> A. x e. RR+ A <_ ( B + ( C x. x ) ) ) )

  proof
    wph
    cA
    cB
    cle
    wbr
    #
    cA
    cB
    cC
    vx
    cv
    #
    cmul
    co
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
    wph
    @0
    @5
    wph
    @0
    wa
    #
    @4
    vx
    crp
    @6
    @1
    crp
    wcel
    #
    wa
    #
    cA
    cB
    @3
    wph
    cA
    cxr
    wcel
    #
    @0
    @7
    xralrple3.a
    ad2antrr
    wph
    cB
    cxr
    wcel
    @0
    @7
    wph
    cB
    xralrple3.b
    rexrd
    ad2antrr
    @8
    @3
    @8
    cB
    @2
    wph
    cB
    cr
    wcel
    #
    @0
    @7
    xralrple3.b
    ad2antrr
    @8
    cC
    @1
    wph
    cC
    cr
    wcel
    #
    @0
    @7
    xralrple3.c
    ad2antrr
    @7
    @1
    cr
    wcel
    #
    @6
    @1
    rpre
    #
    adantl
    remulcld
    readdcld
    rexrd
    wph
    @0
    @7
    simplr
    wph
    @7
    cB
    @3
    cle
    wbr
    #
    @0
    wph
    @7
    wa
    #
    cc0
    @2
    cle
    wbr
    @14
    @15
    cC
    @1
    wph
    @11
    @7
    xralrple3.c
    adantr
    #
    @7
    @12
    wph
    @13
    adantl
    #
    wph
    cc0
    cC
    cle
    wbr
    #
    @7
    xralrple3.g
    adantr
    @7
    cc0
    @1
    cle
    wbr
    wph
    @1
    rpge0
    adantl
    mulge0d
    @15
    cB
    @2
    wph
    @10
    @7
    xralrple3.b
    adantr
    @15
    cC
    @1
    @16
    @17
    remulcld
    addge01d
    mpbid
    adantlr
    xrletrd
    ralrimiva
    ex
    wph
    @5
    @0
    wph
    @5
    wa
    #
    cC
    cc0
    wceq
    #
    @0
    @19
    @20
    wa
    cA
    cB
    cC
    c1
    cmul
    co
    #
    caddc
    co
    #
    cB
    cle
    @5
    cA
    @22
    cle
    wbr
    #
    wph
    @20
    c1
    crp
    wcel
    @5
    @23
    1rp
    @4
    @23
    vx
    c1
    crp
    @1
    c1
    wceq
    #
    @3
    @22
    cA
    cle
    @24
    @2
    @21
    cB
    caddc
    @1
    c1
    cC
    cmul
    oveq2
    oveq2d
    breq2d
    rspcva
    mpan
    ad2antlr
    wph
    @20
    @22
    cB
    wceq
    @5
    wph
    @20
    wa
    #
    @22
    cB
    cc0
    caddc
    co
    #
    cB
    @20
    @22
    @26
    wceq
    wph
    @20
    @21
    cc0
    cB
    caddc
    @20
    @21
    cc0
    c1
    cmul
    co
    #
    cc0
    cC
    cc0
    c1
    cmul
    oveq1
    @27
    cc0
    wceq
    @20
    cc0
    0cn
    mulid1i
    a1i
    eqtrd
    oveq2d
    adantl
    @25
    cB
    wph
    cB
    cc
    wcel
    @20
    wph
    cB
    xralrple3.b
    recnd
    adantr
    addid1d
    eqtrd
    adantlr
    breqtrd
    @19
    @20
    wn
    #
    cC
    crp
    wcel
    #
    @0
    wph
    @28
    @29
    @5
    wph
    @28
    cC
    cc0
    wne
    #
    @29
    @28
    @30
    wph
    cC
    cc0
    neqne
    adantl
    wph
    @30
    wa
    #
    cC
    wph
    @11
    @30
    xralrple3.c
    adantr
    #
    @31
    cc0
    cC
    @31
    0red
    @32
    wph
    @18
    @30
    xralrple3.g
    adantr
    wph
    @30
    simpr
    leneltd
    elrpd
    syldan
    adantlr
    @19
    @29
    wa
    #
    @0
    cA
    cB
    vy
    cv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vy
    crp
    wral
    #
    @33
    @36
    vy
    crp
    @33
    @34
    crp
    wcel
    #
    wa
    #
    cA
    cB
    cC
    @34
    cC
    cdiv
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @35
    cle
    @5
    @29
    @38
    cA
    @42
    cle
    wbr
    #
    wph
    @5
    @29
    wa
    @38
    wa
    @40
    crp
    wcel
    #
    @5
    @43
    @29
    @38
    @44
    @5
    @29
    @38
    wa
    #
    @34
    cC
    @29
    @38
    simpr
    #
    @29
    @38
    simpl
    #
    rpdivcld
    adantll
    @5
    @29
    @38
    simpll
    @4
    @43
    vx
    @40
    crp
    @1
    @40
    wceq
    #
    @3
    @42
    cA
    cle
    @48
    @2
    @41
    cB
    caddc
    @1
    @40
    cC
    cmul
    oveq2
    oveq2d
    breq2d
    rspcva
    syl2anc
    adantlll
    @39
    @41
    @34
    cB
    caddc
    @29
    @38
    @41
    @34
    wceq
    @19
    @45
    @34
    cC
    @45
    @34
    @46
    rpcnd
    @45
    cC
    @47
    rpcnd
    @45
    cC
    @47
    rpne0d
    divcan2d
    adantll
    oveq2d
    breqtrd
    ralrimiva
    wph
    @0
    @37
    wb
    #
    @5
    @29
    wph
    @9
    @10
    @49
    xralrple3.a
    xralrple3.b
    vy
    cA
    cB
    xralrple
    syl2anc
    ad2antrr
    mpbird
    syldan
    pm2.61dan
    ex
    impbid
end
