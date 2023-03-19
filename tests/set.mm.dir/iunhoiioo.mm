include "c0.mm"
include "wceq.mm"
include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cico.mm"
include "cixp.mm"
include "ciun.mm"
include "cioo.mm"
include "csn.mm"
include "wne.mm"
include "nnn0.mm"
include "iunconst.mm"
include "ax-mp.mm"
include "a1i.mm"
include "wcel.mm"
include "ixpeq1.mm"
include "ixp0x.mm"
include "eqtrd.mm"
include "adantr.mm"
include "iuneq2dv.mm"
include "3eqtr4d.mm"
include "adantl.mm"
include "wn.mm"
include "wa.mm"
include "wss.mm"
include "wral.mm"
include "nfv.mm"
include "nfan.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "rexrd.mm"
include "adantlr.mm"
include "cr.mm"
include "crp.mm"
include "nnrp.mm"
include "ad2antlr.mm"
include "rpreccld.mm"
include "ltaddrpd.mm"
include "xrleid.mm"
include "syl.mm"
include "icossioo.mm"
include "syl22anc.mm"
include "ixpssixp.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "cfv.mm"
include "cmin.mm"
include "cmpt.mm"
include "crn.mm"
include "cinf.mm"
include "nfcv.mm"
include "nfixp1.mm"
include "nfel.mm"
include "cfn.mm"
include "ad2antrr.mm"
include "neqne.mm"
include "ad4ant14.mm"
include "simpr.mm"
include "eqid.mm"
include "iunhoiioolem.mm"
include "dfss3.mm"
include "eqssd.mm"
include "pm2.61dan.mm"

theorem iunhoiioo
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  assume iunhoiioo.k: |- F/ k ph
  assume iunhoiioo.x: |- ( ph -> X e. Fin )
  assume iunhoiioo.a: |- ( ( ph /\ k e. X ) -> A e. RR )
  assume iunhoiioo.b: |- ( ( ph /\ k e. X ) -> B e. RR* )

  disjoint A n
  disjoint B n
  disjoint X k
  disjoint X n
  disjoint k n
  disjoint n ph
  disjoint A f
  disjoint f n
  disjoint B f
  disjoint X f
  disjoint f k
  disjoint f ph
  disjoint k x
  assert |- ( ph -> U_ n e. NN X_ k e. X ( ( A + ( 1 / n ) ) [,) B ) = X_ k e. X ( A (,) B ) )

  proof
    wph
    cX
    c0
    wceq
    #
    vn
    cn
    vk
    cX
    cA
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
    cB
    cico
    co
    #
    cixp
    #
    ciun
    #
    vk
    cX
    cA
    cB
    cioo
    co
    #
    cixp
    #
    wceq
    #
    @0
    @9
    wph
    @0
    vn
    cn
    c0
    csn
    #
    ciun
    #
    @10
    @6
    @8
    @11
    @10
    wceq
    #
    @0
    cn
    c0
    wne
    @12
    nnn0
    vn
    cn
    @10
    iunconst
    ax-mp
    a1i
    @0
    vn
    cn
    @5
    @10
    @0
    @5
    @10
    wceq
    @1
    cn
    wcel
    #
    @0
    @5
    vk
    c0
    @4
    cixp
    #
    @10
    vk
    cX
    c0
    @4
    ixpeq1
    @14
    @10
    wceq
    @0
    vk
    @4
    ixp0x
    a1i
    eqtrd
    adantr
    iuneq2dv
    @0
    @8
    vk
    c0
    @7
    cixp
    #
    @10
    vk
    cX
    c0
    @7
    ixpeq1
    @15
    @10
    wceq
    @0
    vk
    @7
    ixp0x
    a1i
    eqtrd
    3eqtr4d
    adantl
    wph
    @0
    wn
    #
    wa
    #
    @6
    @8
    wph
    @6
    @8
    wss
    #
    @16
    wph
    @5
    @8
    wss
    #
    vn
    cn
    wral
    @18
    wph
    @19
    vn
    cn
    wph
    @13
    wa
    #
    vk
    cX
    @4
    @7
    wph
    @13
    vk
    iunhoiioo.k
    @13
    vk
    nfv
    nfan
    @20
    vk
    cv
    #
    cX
    wcel
    #
    wa
    #
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    @3
    clt
    wbr
    cB
    cB
    cle
    wbr
    #
    @4
    @7
    wss
    wph
    @22
    @24
    @13
    wph
    @22
    wa
    #
    cA
    iunhoiioo.a
    rexrd
    adantlr
    wph
    @22
    @25
    @13
    iunhoiioo.b
    adantlr
    @23
    cA
    @2
    wph
    @22
    cA
    cr
    wcel
    #
    @13
    iunhoiioo.a
    adantlr
    @23
    @1
    @13
    @1
    crp
    wcel
    wph
    @22
    @1
    nnrp
    ad2antlr
    rpreccld
    ltaddrpd
    wph
    @22
    @26
    @13
    @27
    @25
    @26
    iunhoiioo.b
    cB
    xrleid
    syl
    adantlr
    cA
    cB
    @3
    cB
    icossioo
    syl22anc
    ixpssixp
    ralrimiva
    vn
    cn
    @5
    @8
    iunss
    sylibr
    adantr
    @17
    vf
    cv
    #
    @6
    wcel
    #
    vf
    @8
    wral
    @8
    @6
    wss
    @17
    @30
    vf
    @8
    @17
    @29
    @8
    wcel
    #
    wa
    cA
    cB
    vk
    cX
    @21
    @29
    cfv
    cA
    cmin
    co
    cmpt
    crn
    cr
    clt
    cinf
    #
    vk
    vn
    @29
    cX
    @17
    @31
    vk
    wph
    @16
    vk
    iunhoiioo.k
    @16
    vk
    nfv
    nfan
    vk
    @29
    @8
    vk
    @29
    nfcv
    vk
    cX
    @7
    nfixp1
    nfel
    nfan
    wph
    cX
    cfn
    wcel
    @16
    @31
    iunhoiioo.x
    ad2antrr
    @16
    cX
    c0
    wne
    wph
    @31
    cX
    c0
    neqne
    ad2antlr
    wph
    @22
    @28
    @16
    @31
    iunhoiioo.a
    ad4ant14
    wph
    @22
    @25
    @16
    @31
    iunhoiioo.b
    ad4ant14
    @17
    @31
    simpr
    @32
    eqid
    iunhoiioolem
    ralrimiva
    vf
    @8
    @6
    dfss3
    sylibr
    eqssd
    pm2.61dan
end
