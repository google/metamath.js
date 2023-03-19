include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "clt.mm"
include "ciin.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "simpllr.mm"
include "cxr.mm"
include "ad2antrr.mm"
include "cr.mm"
include "ad3antrrr.mm"
include "rexrd.mm"
include "adantr.mm"
include "nnrecre.mm"
include "adantl.mm"
include "readdcld.mm"
include "ad4ant14.mm"
include "simplr.mm"
include "crp.mm"
include "nnrp.mm"
include "rpreccl.mm"
include "syl.mm"
include "ltaddrpd.mm"
include "xrlelttrd.mm"
include "jca.mm"
include "rabid.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "ex.mm"
include "ralrimi.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfiin.mm"
include "rabssf.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "nnn0.mm"
include "a1i.mm"
include "iinrab.mm"
include "ad4ant13.mm"
include "simpr.mm"
include "xrltled.mm"
include "ralimdva.mm"
include "imp.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "xrralrecnnle.mm"
include "mpbird.mm"
include "ss2rab.mm"
include "eqsstrd.mm"
include "eqssd.mm"

theorem preimaleiinlt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vn: setvar n
  let vk: setvar k
  assume preimaleiinlt.x: |- F/ x ph
  assume preimaleiinlt.b: |- ( ( ph /\ x e. A ) -> B e. RR* )
  assume preimaleiinlt.c: |- ( ph -> C e. RR )

  disjoint A n
  disjoint B n
  disjoint C n
  disjoint n ph
  disjoint n x
  disjoint k x
  assert |- ( ph -> { x e. A | B <_ C } = |^|_ n e. NN { x e. A | B < ( C + ( 1 / n ) ) } )

  proof
    wph
    cB
    cC
    cle
    wbr
    #
    vx
    cA
    crab
    #
    vn
    cn
    cB
    cC
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
    clt
    wbr
    #
    vx
    cA
    crab
    #
    ciin
    #
    wph
    @0
    vx
    cv
    #
    @7
    wcel
    #
    wi
    #
    vx
    cA
    wral
    @1
    @7
    wss
    wph
    @10
    vx
    cA
    preimaleiinlt.x
    wph
    @8
    cA
    wcel
    #
    @10
    wph
    @11
    wa
    #
    @0
    @9
    @12
    @0
    wa
    #
    @8
    @6
    wcel
    #
    vn
    cn
    wral
    #
    @9
    @13
    @14
    vn
    cn
    @13
    @2
    cn
    wcel
    #
    wa
    #
    @11
    @5
    wa
    @14
    @17
    @11
    @5
    wph
    @11
    @0
    @16
    simpllr
    @17
    cB
    cC
    @4
    @12
    cB
    cxr
    wcel
    #
    @0
    @16
    preimaleiinlt.b
    ad2antrr
    @17
    cC
    wph
    cC
    cr
    wcel
    #
    @11
    @0
    @16
    preimaleiinlt.c
    ad3antrrr
    rexrd
    @17
    @4
    wph
    @16
    @4
    cr
    wcel
    #
    @11
    @0
    wph
    @16
    wa
    #
    cC
    @3
    wph
    @19
    @16
    preimaleiinlt.c
    adantr
    #
    @16
    @3
    cr
    wcel
    wph
    @2
    nnrecre
    adantl
    readdcld
    #
    ad4ant14
    rexrd
    @12
    @0
    @16
    simplr
    wph
    @16
    cC
    @4
    clt
    wbr
    @11
    @0
    @21
    cC
    @3
    @22
    @16
    @3
    crp
    wcel
    #
    wph
    @16
    @2
    crp
    wcel
    @24
    @2
    nnrp
    @2
    rpreccl
    syl
    adantl
    ltaddrpd
    ad4ant14
    xrlelttrd
    jca
    @5
    vx
    cA
    rabid
    sylibr
    ralrimiva
    @8
    cvv
    wcel
    @9
    @15
    wb
    vx
    vex
    vn
    @8
    cn
    @6
    cvv
    eliin
    ax-mp
    sylibr
    ex
    ex
    ralrimi
    @0
    vx
    cA
    @7
    vn
    vx
    cn
    @6
    vx
    cn
    nfcv
    @5
    vx
    cA
    nfrab1
    nfiin
    rabssf
    sylibr
    wph
    @7
    @5
    vn
    cn
    wral
    #
    vx
    cA
    crab
    #
    @1
    wph
    cn
    c0
    wne
    #
    @7
    @26
    wceq
    @27
    wph
    nnn0
    a1i
    @5
    vn
    vx
    cn
    cA
    iinrab
    syl
    wph
    @25
    @0
    wi
    #
    vx
    cA
    wral
    @26
    @1
    wss
    wph
    @28
    vx
    cA
    preimaleiinlt.x
    wph
    @11
    @28
    @12
    @25
    @0
    @12
    @25
    wa
    #
    @0
    cB
    @4
    cle
    wbr
    #
    vn
    cn
    wral
    #
    @12
    @25
    @31
    @12
    @5
    @30
    vn
    cn
    @12
    @16
    wa
    #
    @5
    @30
    @32
    @5
    wa
    #
    cB
    @4
    @12
    @18
    @16
    @5
    preimaleiinlt.b
    ad2antrr
    @33
    @4
    wph
    @16
    @20
    @11
    @5
    @23
    ad4ant13
    rexrd
    @32
    @5
    simpr
    xrltled
    ex
    ralimdva
    imp
    @29
    cB
    cC
    vn
    @12
    @25
    vn
    @12
    vn
    nfv
    @5
    vn
    cn
    nfra1
    nfan
    @12
    @18
    @25
    preimaleiinlt.b
    adantr
    wph
    @19
    @11
    @25
    preimaleiinlt.c
    ad2antrr
    xrralrecnnle
    mpbird
    ex
    ex
    ralrimi
    @25
    @0
    vx
    cA
    ss2rab
    sylibr
    eqsstrd
    eqssd
end
