include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cico.mm"
include "cixp.mm"
include "wcel.mm"
include "cn.mm"
include "wrex.mm"
include "ciun.mm"
include "clt.mm"
include "wbr.mm"
include "crp.mm"
include "cfv.mm"
include "cmin.mm"
include "cmpt.mm"
include "crn.mm"
include "eqid.mm"
include "wa.mm"
include "cr.mm"
include "cioo.mm"
include "wf.mm"
include "ixpf.mm"
include "syl.mm"
include "wss.mm"
include "wral.mm"
include "ioossre.mm"
include "rgenw.mm"
include "a1i.mm"
include "iunss.mm"
include "sylibr.mm"
include "fssd.mm"
include "ffvelrnda.mm"
include "resubcld.mm"
include "cc0.mm"
include "cxr.mm"
include "rexrd.mm"
include "adantr.mm"
include "simpr.mm"
include "fvixp2.mm"
include "syl2anc.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "posdifd.mm"
include "mpbid.mm"
include "elrpd.mm"
include "rnmptssd.mm"
include "cinf.mm"
include "wor.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "ltso.mm"
include "rnmptfi.mm"
include "rnmptn0.mm"
include "fiinfcl.mm"
include "syl13anc.mm"
include "syl5eqel.mm"
include "sseldd.mm"
include "rpgtrecnn.mm"
include "cvv.mm"
include "wfn.mm"
include "w3a.mm"
include "elexd.mm"
include "ad2antrr.mm"
include "ffnd.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfinf.mm"
include "nfcxfr.mm"
include "nfbr.mm"
include "adantlr.mm"
include "nnrecre.mm"
include "ad2antlr.mm"
include "readdcld.mm"
include "ressxr.mm"
include "ad4ant14.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "cle.mm"
include "id.mm"
include "ovexd.mm"
include "elrnmpt1.mm"
include "adantl.mm"
include "infrefilb.mm"
include "syl5eqbr.mm"
include "ltletrd.mm"
include "ltaddsub2d.mm"
include "mpbird.mm"
include "ltled.mm"
include "iooltub.mm"
include "elicod.mm"
include "ex.mm"
include "ralrimi.mm"
include "3jca.mm"
include "elixp2.mm"
include "reximdva.mm"
include "mpd.mm"
include "eliun.mm"

theorem iunhoiioolem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cX: class X
  let vx: setvar x
  assume iunhoiioolem.K: |- F/ k ph
  assume iunhoiioolem.x: |- ( ph -> X e. Fin )
  assume iunhoiioolem.n: |- ( ph -> X =/= (/) )
  assume iunhoiioolem.a: |- ( ( ph /\ k e. X ) -> A e. RR )
  assume iunhoiioolem.b: |- ( ( ph /\ k e. X ) -> B e. RR* )
  assume iunhoiioolem.f: |- ( ph -> F e. X_ k e. X ( A (,) B ) )
  assume iunhoiioolem.c: |- C = inf ( ran ( k e. X |-> ( ( F ` k ) - A ) ) , RR , < )

  disjoint C n
  disjoint F k
  disjoint F n
  disjoint k n
  disjoint X k
  disjoint n ph
  disjoint k x
  assert |- ( ph -> F e. U_ n e. NN X_ k e. X ( ( A + ( 1 / n ) ) [,) B ) )

  proof
    wph
    cF
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
    wcel
    #
    vn
    cn
    wrex
    #
    cF
    vn
    cn
    @4
    ciun
    wcel
    wph
    @1
    cC
    clt
    wbr
    #
    vn
    cn
    wrex
    #
    @6
    wph
    cC
    crp
    wcel
    @8
    wph
    vk
    cX
    vk
    cv
    #
    cF
    cfv
    #
    cA
    cmin
    co
    #
    cmpt
    #
    crn
    #
    crp
    cC
    wph
    vk
    cX
    @11
    crp
    @12
    iunhoiioolem.K
    @12
    eqid
    #
    wph
    @9
    cX
    wcel
    #
    wa
    #
    @11
    @16
    @10
    cA
    wph
    cX
    cr
    @9
    cF
    wph
    cX
    vk
    cX
    cA
    cB
    cioo
    co
    #
    ciun
    #
    cr
    cF
    wph
    cF
    vk
    cX
    @17
    cixp
    #
    wcel
    #
    cX
    @18
    cF
    wf
    iunhoiioolem.f
    vk
    cX
    @17
    cF
    ixpf
    syl
    #
    wph
    @17
    cr
    wss
    #
    vk
    cX
    wral
    #
    @18
    cr
    wss
    @23
    wph
    @22
    vk
    cX
    cA
    cB
    ioossre
    rgenw
    a1i
    vk
    cX
    @17
    cr
    iunss
    sylibr
    fssd
    #
    ffvelrnda
    #
    iunhoiioolem.a
    resubcld
    #
    @16
    cA
    @10
    clt
    wbr
    #
    cc0
    @11
    clt
    wbr
    @16
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @10
    @17
    wcel
    #
    @27
    @16
    cA
    iunhoiioolem.a
    rexrd
    #
    iunhoiioolem.b
    @16
    @20
    @15
    @30
    wph
    @20
    @15
    iunhoiioolem.f
    adantr
    wph
    @15
    simpr
    vk
    cX
    @17
    cF
    fvixp2
    syl2anc
    #
    cA
    cB
    @10
    ioogtlb
    syl3anc
    @16
    cA
    @10
    iunhoiioolem.a
    @25
    posdifd
    mpbid
    elrpd
    #
    rnmptssd
    wph
    cC
    @13
    cr
    clt
    cinf
    #
    @13
    iunhoiioolem.c
    wph
    cr
    clt
    wor
    #
    @13
    cfn
    wcel
    #
    @13
    c0
    wne
    @13
    cr
    wss
    #
    @34
    @13
    wcel
    @35
    wph
    ltso
    a1i
    wph
    cX
    cfn
    wcel
    @36
    iunhoiioolem.x
    vk
    @12
    cX
    @11
    @14
    rnmptfi
    syl
    #
    wph
    vk
    cX
    @11
    @12
    crp
    iunhoiioolem.K
    @33
    @14
    iunhoiioolem.n
    rnmptn0
    wph
    vk
    cX
    @11
    cr
    @12
    iunhoiioolem.K
    @14
    @26
    rnmptssd
    #
    cr
    @13
    clt
    fiinfcl
    syl13anc
    syl5eqel
    #
    sseldd
    cC
    vn
    rpgtrecnn
    syl
    wph
    @7
    @5
    vn
    cn
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @7
    @5
    @42
    @7
    wa
    #
    cF
    cvv
    wcel
    #
    cF
    cX
    wfn
    #
    @10
    @3
    wcel
    #
    vk
    cX
    wral
    #
    w3a
    @5
    @43
    @44
    @45
    @47
    wph
    @44
    @41
    @7
    wph
    cF
    @19
    iunhoiioolem.f
    elexd
    ad2antrr
    wph
    @45
    @41
    @7
    wph
    cX
    @18
    cF
    @21
    ffnd
    ad2antrr
    @43
    @46
    vk
    cX
    @42
    @7
    vk
    wph
    @41
    vk
    iunhoiioolem.K
    @41
    vk
    nfv
    nfan
    vk
    @1
    cC
    clt
    vk
    @1
    nfcv
    vk
    clt
    nfcv
    #
    vk
    cC
    @34
    iunhoiioolem.c
    vk
    @13
    cr
    clt
    vk
    @12
    vk
    cX
    @11
    nfmpt1
    nfrn
    vk
    cr
    nfcv
    @48
    nfinf
    nfcxfr
    nfbr
    nfan
    @43
    @15
    @46
    @43
    @15
    wa
    #
    @2
    cB
    @10
    @42
    @15
    @2
    cxr
    wcel
    @7
    @42
    @15
    wa
    #
    @2
    @50
    cA
    @1
    wph
    @15
    cA
    cr
    wcel
    #
    @41
    iunhoiioolem.a
    adantlr
    #
    @41
    @1
    cr
    wcel
    #
    wph
    @15
    @0
    nnrecre
    ad2antlr
    #
    readdcld
    #
    rexrd
    adantlr
    @42
    @15
    @29
    @7
    wph
    @15
    @29
    @41
    iunhoiioolem.b
    adantlr
    adantlr
    @43
    cX
    cxr
    @9
    cF
    wph
    cX
    cxr
    cF
    wf
    @41
    @7
    wph
    cX
    cr
    cxr
    cF
    @24
    cr
    cxr
    wss
    wph
    ressxr
    a1i
    fssd
    ad2antrr
    ffvelrnda
    @49
    @2
    @10
    @42
    @15
    @2
    cr
    wcel
    @7
    @55
    adantlr
    wph
    @15
    @10
    cr
    wcel
    @41
    @7
    @25
    ad4ant14
    #
    @49
    @2
    @10
    clt
    wbr
    @1
    @11
    clt
    wbr
    @49
    @1
    cC
    @11
    @42
    @15
    @53
    @7
    @54
    adantlr
    #
    wph
    cC
    cr
    wcel
    @41
    @7
    @15
    wph
    @13
    cr
    cC
    @39
    @40
    sseldd
    ad3antrrr
    wph
    @15
    @11
    cr
    wcel
    @41
    @7
    @26
    ad4ant14
    @42
    @7
    @15
    simplr
    @42
    @15
    cC
    @11
    cle
    wbr
    @7
    @50
    cC
    @34
    @11
    cle
    iunhoiioolem.c
    @50
    @37
    @36
    @11
    @13
    wcel
    #
    @34
    @11
    cle
    wbr
    wph
    @37
    @41
    @15
    @39
    ad2antrr
    wph
    @36
    @41
    @15
    @38
    ad2antrr
    @15
    @58
    @42
    @15
    @15
    @11
    cvv
    wcel
    @58
    @15
    id
    @15
    @10
    cA
    cmin
    ovexd
    vk
    cX
    @11
    @12
    cvv
    @14
    elrnmpt1
    syl2anc
    adantl
    @11
    @13
    infrefilb
    syl3anc
    syl5eqbr
    adantlr
    ltletrd
    @49
    cA
    @1
    @10
    @42
    @15
    @51
    @7
    @52
    adantlr
    @57
    @56
    ltaddsub2d
    mpbird
    ltled
    wph
    @15
    @10
    cB
    clt
    wbr
    #
    @41
    @7
    @16
    @28
    @29
    @30
    @59
    @31
    iunhoiioolem.b
    @32
    cA
    cB
    @10
    iooltub
    syl3anc
    ad4ant14
    elicod
    ex
    ralrimi
    3jca
    vk
    cX
    @3
    cF
    elixp2
    sylibr
    ex
    reximdva
    mpd
    vn
    cF
    cn
    @4
    eliun
    sylibr
end
