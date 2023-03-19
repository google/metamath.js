include "cvv.mm"
include "wcel.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cicc.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "cixp.mm"
include "cn.mm"
include "c1.mm"
include "cdiv.mm"
include "caddc.mm"
include "cico.mm"
include "ciin.mm"
include "elexd.mm"
include "cr.mm"
include "wf.mm"
include "wss.mm"
include "wrex.mm"
include "1nn.mm"
include "a1i.mm"
include "wa.mm"
include "cxr.mm"
include "peano2re.mm"
include "syl.mm"
include "rexrd.mm"
include "icossre.mm"
include "syl2anc.mm"
include "ixpssixp.mm"
include "wceq.mm"
include "oveq2.mm"
include "1div1e1.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "ixpeq2dv.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "iinss.mm"
include "sseldd.mm"
include "wb.mm"
include "elixpconstg.mm"
include "mpbid.mm"
include "ffnd.mm"
include "ffvelrnda.mm"
include "cle.mm"
include "wbr.mm"
include "ssid.mm"
include "adantr.mm"
include "simpr.mm"
include "fvixp2.mm"
include "icogelb.mm"
include "syl3anc.mm"
include "nnrecre.mm"
include "adantl.mm"
include "readdcld.mm"
include "clt.mm"
include "ressxr.mm"
include "sseldi.mm"
include "eliin.mm"
include "r19.21bi.mm"
include "elixp2.mm"
include "sylib.mm"
include "simp3d.mm"
include "an32s.mm"
include "icoltub.mm"
include "ltled.mm"
include "ralrimiva.mm"
include "nfv.mm"
include "xrralrecnnle.mm"
include "mpbird.mm"
include "eliccd.mm"
include "ex.mm"
include "ralrimi.mm"
include "3jca.mm"
include "sylibr.mm"

theorem iinhoiicclem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cX: class X
  let vx: setvar x
  assume iinhoiicclem.k: |- F/ k ph
  assume iinhoiicclem.a: |- ( ( ph /\ k e. X ) -> A e. RR )
  assume iinhoiicclem.b: |- ( ( ph /\ k e. X ) -> B e. RR )
  assume iinhoiicclem.f: |- ( ph -> F e. |^|_ n e. NN X_ k e. X ( A [,) ( B + ( 1 / n ) ) ) )

  disjoint A n
  disjoint B n
  disjoint F k
  disjoint F n
  disjoint k n
  disjoint X k
  disjoint X n
  disjoint n ph
  disjoint k x
  assert |- ( ph -> F e. X_ k e. X ( A [,] B ) )

  proof
    wph
    cF
    cvv
    wcel
    #
    cF
    cX
    wfn
    #
    vk
    cv
    #
    cF
    cfv
    #
    cA
    cB
    cicc
    co
    #
    wcel
    #
    vk
    cX
    wral
    #
    w3a
    cF
    vk
    cX
    @4
    cixp
    wcel
    wph
    @0
    @1
    @6
    wph
    cF
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
    iinhoiicclem.f
    elexd
    #
    wph
    cX
    cr
    cF
    wph
    cF
    vk
    cX
    cr
    cixp
    #
    wcel
    #
    cX
    cr
    cF
    wf
    #
    wph
    @12
    @14
    cF
    wph
    @11
    @14
    wss
    #
    vn
    cn
    wrex
    #
    @12
    @14
    wss
    wph
    c1
    cn
    wcel
    #
    vk
    cX
    cA
    cB
    c1
    caddc
    co
    #
    cico
    co
    #
    cixp
    #
    @14
    wss
    #
    @18
    @19
    wph
    1nn
    a1i
    #
    wph
    vk
    cX
    @21
    cr
    iinhoiicclem.k
    wph
    @2
    cX
    wcel
    #
    wa
    #
    cA
    cr
    wcel
    @20
    cxr
    wcel
    #
    @21
    cr
    wss
    iinhoiicclem.a
    @26
    @20
    @26
    cB
    cr
    wcel
    #
    @20
    cr
    wcel
    iinhoiicclem.b
    cB
    peano2re
    syl
    rexrd
    #
    cA
    @20
    icossre
    syl2anc
    ixpssixp
    @17
    @23
    vn
    c1
    cn
    @7
    c1
    wceq
    #
    @11
    @22
    @14
    @30
    vk
    cX
    @10
    @21
    @30
    @9
    @20
    cA
    cico
    @30
    @8
    c1
    cB
    caddc
    @30
    @8
    c1
    c1
    cdiv
    co
    #
    c1
    @7
    c1
    c1
    cdiv
    oveq2
    @31
    c1
    wceq
    @30
    1div1e1
    a1i
    eqtrd
    oveq2d
    oveq2d
    ixpeq2dv
    #
    sseq1d
    rspcev
    syl2anc
    vn
    cn
    @11
    @14
    iinss
    syl
    iinhoiicclem.f
    sseldd
    wph
    cF
    @12
    wcel
    #
    @15
    @16
    wb
    iinhoiicclem.f
    vk
    cX
    cr
    cF
    @12
    elixpconstg
    syl
    mpbid
    #
    ffnd
    wph
    @5
    vk
    cX
    iinhoiicclem.k
    wph
    @25
    @5
    @26
    cA
    cB
    @3
    iinhoiicclem.a
    iinhoiicclem.b
    wph
    cX
    cr
    @2
    cF
    @34
    ffvelrnda
    #
    @26
    cA
    cxr
    wcel
    #
    @27
    @3
    @21
    wcel
    #
    cA
    @3
    cle
    wbr
    @26
    cA
    iinhoiicclem.a
    rexrd
    #
    @29
    @26
    cF
    @22
    wcel
    #
    @25
    @37
    wph
    @39
    @25
    wph
    @12
    @22
    cF
    wph
    @11
    @22
    wss
    #
    vn
    cn
    wrex
    #
    @12
    @22
    wss
    wph
    @19
    @22
    @22
    wss
    #
    @41
    @24
    @42
    wph
    @22
    ssid
    a1i
    @40
    @42
    vn
    c1
    cn
    @30
    @11
    @22
    @22
    @32
    sseq1d
    rspcev
    syl2anc
    vn
    cn
    @11
    @22
    iinss
    syl
    iinhoiicclem.f
    sseldd
    adantr
    wph
    @25
    simpr
    vk
    cX
    @21
    cF
    fvixp2
    syl2anc
    cA
    @20
    @3
    icogelb
    syl3anc
    @26
    @3
    cB
    cle
    wbr
    @3
    @9
    cle
    wbr
    #
    vn
    cn
    wral
    @26
    @43
    vn
    cn
    @26
    @7
    cn
    wcel
    #
    wa
    #
    @3
    @9
    @26
    @3
    cr
    wcel
    @44
    @35
    adantr
    @45
    cB
    @8
    @26
    @28
    @44
    iinhoiicclem.b
    adantr
    @44
    @8
    cr
    wcel
    @26
    @7
    nnrecre
    adantl
    readdcld
    #
    @45
    @36
    @9
    cxr
    wcel
    @3
    @10
    wcel
    #
    @3
    @9
    clt
    wbr
    @26
    @36
    @44
    @38
    adantr
    @45
    cr
    cxr
    @9
    ressxr
    @46
    sseldi
    wph
    @44
    @25
    @47
    wph
    @44
    wa
    #
    @47
    vk
    cX
    @48
    @0
    @1
    @47
    vk
    cX
    wral
    #
    @48
    cF
    @11
    wcel
    #
    @0
    @1
    @49
    w3a
    wph
    @50
    vn
    cn
    wph
    @33
    @50
    vn
    cn
    wral
    #
    iinhoiicclem.f
    wph
    @0
    @33
    @51
    wb
    @13
    vn
    cF
    cn
    @11
    cvv
    eliin
    syl
    mpbid
    r19.21bi
    vk
    cX
    @10
    cF
    elixp2
    sylib
    simp3d
    r19.21bi
    an32s
    cA
    @9
    @3
    icoltub
    syl3anc
    ltled
    ralrimiva
    @26
    @3
    cB
    vn
    @26
    vn
    nfv
    @26
    cr
    cxr
    @3
    ressxr
    @35
    sseldi
    iinhoiicclem.b
    xrralrecnnle
    mpbird
    eliccd
    ex
    ralrimi
    3jca
    vk
    cX
    @4
    cF
    elixp2
    sylibr
end
