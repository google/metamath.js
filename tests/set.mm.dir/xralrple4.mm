include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cexp.mm"
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
include "cn0.mm"
include "nnnn0d.mm"
include "adantr.mm"
include "reexpcld.mm"
include "adantlr.mm"
include "readdcld.mm"
include "simplr.mm"
include "cc0.mm"
include "rpge0.mm"
include "expge0d.mm"
include "addge01d.mm"
include "mpbid.mm"
include "xrletrd.mm"
include "ralrimiva.mm"
include "ex.mm"
include "c1.mm"
include "cdiv.mm"
include "ccxp.mm"
include "simpr.mm"
include "nnrpd.mm"
include "rpreccld.mm"
include "rpred.mm"
include "rpcxpcld.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "breq2d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "cc.mm"
include "cn.mm"
include "rpcnd.mm"
include "cxproot.mm"
include "breqtrd.mm"
include "wb.mm"
include "xralrple.mm"
include "mpbird.mm"
include "impbid.mm"

theorem xralrple4
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cN: class N
  let vy: setvar y
  assume xralrple4.a: |- ( ph -> A e. RR* )
  assume xralrple4.b: |- ( ph -> B e. RR )
  assume xralrple4.n: |- ( ph -> N e. NN )

  disjoint A x
  disjoint B x
  disjoint N x
  disjoint ph x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint N y
  disjoint ph y
  assert |- ( ph -> ( A <_ B <-> A. x e. RR+ A <_ ( B + ( x ^ N ) ) ) )

  proof
    wph
    cA
    cB
    cle
    wbr
    #
    cA
    cB
    vx
    cv
    #
    cN
    cexp
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
    xralrple4.a
    ad2antrr
    wph
    cB
    cxr
    wcel
    @0
    @7
    wph
    cB
    xralrple4.b
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
    xralrple4.b
    ad2antrr
    wph
    @7
    @2
    cr
    wcel
    @0
    wph
    @7
    wa
    #
    @1
    cN
    @7
    @1
    cr
    wcel
    wph
    @1
    rpre
    adantl
    #
    wph
    cN
    cn0
    wcel
    @7
    wph
    cN
    xralrple4.n
    nnnn0d
    adantr
    #
    reexpcld
    #
    adantlr
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
    @11
    cc0
    @2
    cle
    wbr
    @15
    @11
    @1
    cN
    @12
    @13
    @7
    cc0
    @1
    cle
    wbr
    wph
    @1
    rpge0
    adantl
    expge0d
    @11
    cB
    @2
    wph
    @10
    @7
    xralrple4.b
    adantr
    @14
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
    @16
    @19
    vy
    crp
    @16
    @17
    crp
    wcel
    #
    wa
    #
    cA
    cB
    @17
    c1
    cN
    cdiv
    co
    #
    ccxp
    co
    #
    cN
    cexp
    co
    #
    caddc
    co
    #
    @18
    cle
    @22
    @24
    crp
    wcel
    #
    @5
    cA
    @26
    cle
    wbr
    #
    wph
    @21
    @27
    @5
    wph
    @21
    wa
    #
    @17
    @23
    wph
    @21
    simpr
    #
    wph
    @23
    cr
    wcel
    @21
    wph
    @23
    wph
    cN
    wph
    cN
    xralrple4.n
    nnrpd
    rpreccld
    rpred
    adantr
    rpcxpcld
    adantlr
    wph
    @5
    @21
    simplr
    @4
    @28
    vx
    @24
    crp
    @1
    @24
    wceq
    #
    @3
    @26
    cA
    cle
    @31
    @2
    @25
    cB
    caddc
    @1
    @24
    cN
    cexp
    oveq1
    oveq2d
    breq2d
    rspcva
    syl2anc
    wph
    @21
    @26
    @18
    wceq
    @5
    @29
    @25
    @17
    cB
    caddc
    @29
    @17
    cc
    wcel
    cN
    cn
    wcel
    #
    @25
    @17
    wceq
    @29
    @17
    @30
    rpcnd
    wph
    @32
    @21
    xralrple4.n
    adantr
    @17
    cN
    cxproot
    syl2anc
    oveq2d
    adantlr
    breqtrd
    ralrimiva
    wph
    @0
    @20
    wb
    #
    @5
    wph
    @9
    @10
    @33
    xralrple4.a
    xralrple4.b
    vy
    cA
    cB
    xralrple
    syl2anc
    adantr
    mpbird
    ex
    impbid
end
