include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cico.mm"
include "cixp.mm"
include "ciin.mm"
include "cicc.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ixpeq2dv.mm"
include "cbviinv.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "adantl.mm"
include "wa.mm"
include "nfcv.mm"
include "nfixp1.mm"
include "nfiin.mm"
include "nfel.mm"
include "nfan.mm"
include "cr.mm"
include "adantlr.mm"
include "biimpri.mm"
include "iinhoiicclem.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "nfv.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "rexrd.mm"
include "crp.mm"
include "nnrp.mm"
include "ad2antlr.mm"
include "rpreccld.mm"
include "rpred.mm"
include "readdcld.mm"
include "leidd.mm"
include "ltaddrpd.mm"
include "iccssico.mm"
include "syl22anc.mm"
include "ixpssixp.mm"
include "ssiin.mm"
include "eqssd.mm"

theorem iinhoiicc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cX: class X
  let vf: setvar f
  let vm: setvar m
  let vx: setvar x
  assume iunhoiicc.k: |- F/ k ph
  assume iunhoiicc.a: |- ( ( ph /\ k e. X ) -> A e. RR )
  assume iunhoiicc.b: |- ( ( ph /\ k e. X ) -> B e. RR )

  disjoint A n
  disjoint B n
  disjoint X k
  disjoint X n
  disjoint k n
  disjoint n ph
  disjoint A f
  disjoint f n
  disjoint A m
  disjoint m n
  disjoint B f
  disjoint B m
  disjoint X f
  disjoint f k
  disjoint X m
  disjoint k m
  disjoint f ph
  disjoint k x
  assert |- ( ph -> |^|_ n e. NN X_ k e. X ( A [,) ( B + ( 1 / n ) ) ) = X_ k e. X ( A [,] B ) )

  proof
    wph
    vn
    cn
    vk
    cX
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
    cico
    co
    #
    cixp
    #
    ciin
    #
    vk
    cX
    cA
    cB
    cicc
    co
    #
    cixp
    #
    wph
    vf
    cv
    #
    @7
    wcel
    #
    vf
    @5
    wral
    @5
    @7
    wss
    wph
    @9
    vf
    @5
    wph
    @8
    @5
    wcel
    #
    @8
    vm
    cn
    vk
    cX
    cA
    cB
    c1
    vm
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
    cico
    co
    #
    cixp
    #
    ciin
    #
    wcel
    #
    @9
    @10
    @17
    wph
    @10
    @17
    @5
    @16
    @8
    vn
    vm
    cn
    @4
    @15
    @0
    @11
    wceq
    #
    vk
    cX
    @3
    @14
    @18
    @2
    @13
    cA
    cico
    @18
    @1
    @12
    cB
    caddc
    @0
    @11
    c1
    cdiv
    oveq2
    oveq2d
    oveq2d
    ixpeq2dv
    cbviinv
    eleq2i
    #
    biimpi
    adantl
    wph
    @17
    wa
    cA
    cB
    vk
    vn
    @8
    cX
    wph
    @17
    vk
    iunhoiicc.k
    vk
    @8
    @16
    vk
    @8
    nfcv
    vm
    vk
    cn
    @15
    vk
    cn
    nfcv
    vk
    cX
    @14
    nfixp1
    nfiin
    nfel
    nfan
    wph
    vk
    cv
    cX
    wcel
    #
    cA
    cr
    wcel
    #
    @17
    iunhoiicc.a
    adantlr
    wph
    @20
    cB
    cr
    wcel
    #
    @17
    iunhoiicc.b
    adantlr
    @17
    @10
    wph
    @10
    @17
    @19
    biimpri
    adantl
    iinhoiicclem
    syldan
    ralrimiva
    vf
    @5
    @7
    dfss3
    sylibr
    wph
    @7
    @4
    wss
    #
    vn
    cn
    wral
    @7
    @5
    wss
    wph
    @23
    vn
    cn
    wph
    @0
    cn
    wcel
    #
    wa
    #
    vk
    cX
    @6
    @3
    wph
    @24
    vk
    iunhoiicc.k
    @24
    vk
    nfv
    nfan
    @25
    @20
    wa
    #
    cA
    cxr
    wcel
    #
    @2
    cxr
    wcel
    cA
    cA
    cle
    wbr
    cB
    @2
    clt
    wbr
    @6
    @3
    wss
    wph
    @20
    @27
    @24
    wph
    @20
    wa
    cA
    iunhoiicc.a
    rexrd
    adantlr
    @26
    @2
    @26
    cB
    @1
    wph
    @20
    @22
    @24
    iunhoiicc.b
    adantlr
    #
    @26
    @1
    @26
    @0
    @24
    @0
    crp
    wcel
    wph
    @20
    @0
    nnrp
    ad2antlr
    rpreccld
    #
    rpred
    readdcld
    rexrd
    @26
    cA
    wph
    @20
    @21
    @24
    iunhoiicc.a
    adantlr
    leidd
    @26
    cB
    @1
    @28
    @29
    ltaddrpd
    cA
    @2
    cA
    cB
    iccssico
    syl22anc
    ixpssixp
    ralrimiva
    vn
    cn
    @4
    @7
    ssiin
    sylibr
    eqssd
end
