include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cin.mm"
include "crab.mm"
include "cq.mm"
include "cv.mm"
include "cfv.mm"
include "wa.mm"
include "ciun.mm"
include "crest.mm"
include "smfaddlem1.mm"
include "cvv.mm"
include "wcel.mm"
include "elinel1.mm"
include "adantl.mm"
include "ssdf.mm"
include "ssexd.mm"
include "eqid.mm"
include "subsalsal.mm"
include "com.mm"
include "cdom.mm"
include "qct.mm"
include "a1i.mm"
include "csalg.mm"
include "adantr.mm"
include "wss.mm"
include "qex.mm"
include "cmpt.mm"
include "wceq.mm"
include "rabex.mm"
include "fvmpt2d.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "ssdomg.mm"
include "sylc.mm"
include "domtr.mm"
include "syl2anc.mm"
include "inrab.mm"
include "ad2antrr.mm"
include "cr.mm"
include "nfv.mm"
include "nfan.mm"
include "syldan.mm"
include "ad4ant14.mm"
include "csmblfn.mm"
include "sssmfmpt.mm"
include "qre.mm"
include "ad2antlr.mm"
include "smfpimltmpt.mm"
include "elinel2.mm"
include "ssriv.mm"
include "sselda.mm"
include "sseldi.mm"
include "salincld.mm"
include "syl5eqelr.mm"
include "saliuncl.mm"
include "eqeltrd.mm"

theorem smfaddlem2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cK: class K
  let cV: class V
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  assume smfaddlem2.x: |- F/ x ph
  assume smfaddlem2.s: |- ( ph -> S e. SAlg )
  assume smfaddlem2.a: |- ( ph -> A e. V )
  assume smfaddlem2.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume smfaddlem2.d: |- ( ( ph /\ x e. C ) -> D e. RR )
  assume smfaddlem2.m: |- ( ph -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume smfaddlem2.7: |- ( ph -> ( x e. C |-> D ) e. ( SMblFn ` S ) )
  assume smfaddlem2.r: |- ( ph -> R e. RR )
  assume smfaddlem2.k: |- K = ( p e. QQ |-> { q e. QQ | ( p + q ) < R } )

  disjoint A p
  disjoint A q
  disjoint A x
  disjoint p q
  disjoint p x
  disjoint q x
  disjoint B p
  disjoint B q
  disjoint C p
  disjoint C q
  disjoint C x
  disjoint D p
  disjoint D q
  disjoint K q
  disjoint K x
  disjoint R p
  disjoint R q
  disjoint S p
  disjoint S q
  disjoint p ph
  disjoint ph q
  disjoint k x
  assert |- ( ph -> { x e. ( A i^i C ) | ( B + D ) < R } e. ( S |`t ( A i^i C ) ) )

  proof
    wph
    cB
    cD
    caddc
    co
    cR
    clt
    wbr
    vx
    cA
    cC
    cin
    #
    crab
    vp
    cq
    vq
    vp
    cv
    #
    cK
    cfv
    #
    cB
    @1
    clt
    wbr
    #
    cD
    vq
    cv
    #
    clt
    wbr
    #
    wa
    vx
    @0
    crab
    #
    ciun
    #
    ciun
    cS
    @0
    crest
    co
    #
    wph
    vx
    cA
    cB
    cC
    cD
    cR
    cK
    vq
    vp
    smfaddlem2.x
    smfaddlem2.b
    smfaddlem2.d
    smfaddlem2.r
    smfaddlem2.k
    smfaddlem1
    wph
    @8
    vp
    @7
    cq
    wph
    @0
    cS
    @8
    cvv
    smfaddlem2.s
    wph
    @0
    cA
    cV
    smfaddlem2.a
    wph
    vx
    @0
    cA
    smfaddlem2.x
    vx
    cv
    #
    @0
    wcel
    #
    @9
    cA
    wcel
    #
    wph
    @9
    cA
    cC
    elinel1
    adantl
    #
    ssdf
    #
    ssexd
    @8
    eqid
    subsalsal
    #
    cq
    com
    cdom
    wbr
    #
    wph
    qct
    a1i
    wph
    @1
    cq
    wcel
    #
    wa
    #
    @8
    vq
    @6
    @2
    wph
    @8
    csalg
    wcel
    #
    @16
    @14
    adantr
    @17
    @2
    cq
    cdom
    wbr
    #
    @15
    @2
    com
    cdom
    wbr
    @17
    cq
    cvv
    wcel
    #
    @2
    cq
    wss
    @19
    @20
    @17
    qex
    a1i
    @17
    @2
    @1
    @4
    caddc
    co
    cR
    clt
    wbr
    #
    vq
    cq
    crab
    #
    cq
    wph
    vp
    cq
    @22
    cK
    cvv
    cK
    vp
    cq
    @22
    cmpt
    wceq
    wph
    smfaddlem2.k
    a1i
    @22
    cvv
    wcel
    @17
    @21
    vq
    cq
    qex
    rabex
    a1i
    fvmpt2d
    @21
    vq
    cq
    ssrab2
    syl6eqss
    #
    @2
    cq
    cvv
    ssdomg
    sylc
    @15
    @17
    qct
    a1i
    @2
    cq
    com
    domtr
    syl2anc
    @17
    @4
    @2
    wcel
    #
    wa
    #
    @6
    @3
    vx
    @0
    crab
    #
    @5
    vx
    @0
    crab
    #
    cin
    @8
    @3
    @5
    vx
    @0
    inrab
    @25
    @8
    @26
    @27
    wph
    @18
    @16
    @24
    @14
    ad2antrr
    @25
    vx
    @0
    cB
    @1
    cS
    cr
    @17
    @24
    vx
    wph
    @16
    vx
    smfaddlem2.x
    @16
    vx
    nfv
    nfan
    @24
    vx
    nfv
    nfan
    #
    wph
    cS
    csalg
    wcel
    @16
    @24
    smfaddlem2.s
    ad2antrr
    #
    wph
    @10
    cB
    cr
    wcel
    #
    @16
    @24
    wph
    @10
    @11
    @30
    @12
    smfaddlem2.b
    syldan
    ad4ant14
    wph
    vx
    @0
    cB
    cmpt
    cS
    csmblfn
    cfv
    #
    wcel
    @16
    @24
    wph
    vx
    cA
    cB
    @0
    cS
    smfaddlem2.s
    smfaddlem2.m
    @13
    sssmfmpt
    ad2antrr
    @16
    @1
    cr
    wcel
    wph
    @24
    @1
    qre
    #
    ad2antlr
    smfpimltmpt
    @25
    vx
    @0
    cD
    @4
    cS
    cr
    @28
    @29
    wph
    @10
    cD
    cr
    wcel
    #
    @16
    @24
    wph
    @10
    @9
    cC
    wcel
    #
    @33
    @10
    @34
    wph
    @9
    cA
    cC
    elinel2
    adantl
    #
    smfaddlem2.d
    syldan
    ad4ant14
    wph
    vx
    @0
    cD
    cmpt
    @31
    wcel
    @16
    @24
    wph
    vx
    cC
    cD
    @0
    cS
    smfaddlem2.s
    smfaddlem2.7
    wph
    vx
    @0
    cC
    smfaddlem2.x
    @35
    ssdf
    sssmfmpt
    ad2antrr
    @25
    cq
    cr
    @4
    vp
    cq
    cr
    @32
    ssriv
    @17
    @2
    cq
    @4
    @23
    sselda
    sseldi
    smfpimltmpt
    salincld
    syl5eqelr
    saliuncl
    saliuncl
    eqeltrd
end
