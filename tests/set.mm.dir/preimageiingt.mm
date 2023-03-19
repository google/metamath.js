include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "clt.mm"
include "ciin.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "simpllr.mm"
include "cxr.mm"
include "cr.mm"
include "adantr.mm"
include "nnrecre.mm"
include "adantl.mm"
include "resubcld.mm"
include "rexrd.mm"
include "ad4ant14.mm"
include "ad3antrrr.mm"
include "ad2antrr.mm"
include "crp.mm"
include "nnrp.mm"
include "rpreccl.mm"
include "syl.mm"
include "ltsubrpd.mm"
include "simplr.mm"
include "xrltletrd.mm"
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
include "wceq.mm"
include "c0.mm"
include "wne.mm"
include "nnn0.mm"
include "iinrab.mm"
include "a1i.mm"
include "ad4ant13.mm"
include "simpr.mm"
include "xrltled.mm"
include "ralimdva.mm"
include "imp.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "xrralrecnnge.mm"
include "mpbird.mm"
include "ss2rab.mm"
include "eqsstrd.mm"
include "eqssd.mm"

theorem preimageiingt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vn: setvar n
  let vk: setvar k
  assume preimageiingt.x: |- F/ x ph
  assume preimageiingt.b: |- ( ( ph /\ x e. A ) -> B e. RR* )
  assume preimageiingt.c: |- ( ph -> C e. RR )

  disjoint A n
  disjoint B n
  disjoint C n
  disjoint n ph
  disjoint n x
  disjoint k x
  assert |- ( ph -> { x e. A | C <_ B } = |^|_ n e. NN { x e. A | ( C - ( 1 / n ) ) < B } )

  proof
    wph
    cC
    cB
    cle
    wbr
    #
    vx
    cA
    crab
    #
    vn
    cn
    cC
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
    preimageiingt.x
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
    @4
    cC
    cB
    wph
    @16
    @4
    cxr
    wcel
    #
    @11
    @0
    wph
    @16
    wa
    #
    @4
    @19
    cC
    @3
    wph
    cC
    cr
    wcel
    #
    @16
    preimageiingt.c
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
    resubcld
    rexrd
    #
    ad4ant14
    wph
    cC
    cxr
    wcel
    @11
    @0
    @16
    wph
    cC
    preimageiingt.c
    rexrd
    ad3antrrr
    @12
    cB
    cxr
    wcel
    #
    @0
    @16
    preimageiingt.b
    ad2antrr
    wph
    @16
    @4
    cC
    clt
    wbr
    @11
    @0
    @19
    cC
    @3
    @21
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
    ltsubrpd
    ad4ant14
    @12
    @0
    @16
    simplr
    xrltletrd
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
    @7
    @26
    wceq
    #
    wph
    cn
    c0
    wne
    @27
    nnn0
    @5
    vn
    vx
    cn
    cA
    iinrab
    ax-mp
    a1i
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
    preimageiingt.x
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
    @4
    cB
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
    @4
    cB
    wph
    @16
    @18
    @11
    @5
    @22
    ad4ant13
    @12
    @23
    @16
    @5
    preimageiingt.b
    ad2antrr
    @32
    @5
    simpr
    xrltled
    ex
    ralimdva
    imp
    @29
    cC
    cB
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
    wph
    @20
    @11
    @25
    preimageiingt.c
    ad2antrr
    @12
    @23
    @25
    preimageiingt.b
    adantr
    xrralrecnnge
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
