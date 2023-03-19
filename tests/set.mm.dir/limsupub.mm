include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "clt.mm"
include "wn.mm"
include "wa.mm"
include "clsp.mm"
include "cpnf.mm"
include "wceq.mm"
include "wss.mm"
include "adantr.mm"
include "cxr.mm"
include "wf.mm"
include "wcel.mm"
include "nfv.mm"
include "nfan.mm"
include "simprl.mm"
include "simpllr.mm"
include "rexr.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "ad4ant13.mm"
include "simpr.mm"
include "xrltled.mm"
include "adantrl.mm"
include "jca.mm"
include "ex.mm"
include "reximdai.mm"
include "ralimdv.mm"
include "ralimdva.mm"
include "imp.mm"
include "limsuppnfd.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "imnan.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"
include "rexbii.mm"
include "rexnal.mm"
include "sylibr.mm"
include "ad4ant14.mm"
include "rexrd.mm"
include "xrlenltd.mm"
include "imbi2d.mm"
include "ralbida.mm"
include "rexbidva.mm"
include "mpbird.mm"

theorem limsupub
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  assume limsupub.j: |- F/ j ph
  assume limsupub.e: |- F/_ j F
  assume limsupub.a: |- ( ph -> A C_ RR )
  assume limsupub.f: |- ( ph -> F : A --> RR* )
  assume limsupub.n: |- ( ph -> ( limsup ` F ) =/= +oo )

  disjoint A j
  disjoint A k
  disjoint A x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint k ph
  disjoint ph x
  assert |- ( ph -> E. x e. RR E. k e. RR A. j e. A ( k <_ j -> ( F ` j ) <_ x ) )

  proof
    wph
    vk
    cv
    #
    vj
    cv
    #
    cle
    wbr
    #
    @1
    cF
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    wi
    #
    vj
    cA
    wral
    #
    vk
    cr
    wrex
    #
    vx
    cr
    wrex
    @2
    @4
    @3
    clt
    wbr
    #
    wn
    #
    wi
    #
    vj
    cA
    wral
    #
    vk
    cr
    wrex
    #
    vx
    cr
    wrex
    #
    wph
    @2
    @9
    wa
    #
    vj
    cA
    wrex
    #
    vk
    cr
    wral
    #
    vx
    cr
    wral
    #
    wn
    #
    @14
    wph
    @18
    cF
    clsp
    cfv
    #
    cpnf
    wceq
    #
    wph
    @18
    wa
    vx
    cA
    vj
    vk
    cF
    limsupub.e
    wph
    cA
    cr
    wss
    @18
    limsupub.a
    adantr
    wph
    cA
    cxr
    cF
    wf
    @18
    limsupub.f
    adantr
    wph
    @18
    @2
    @4
    @3
    cle
    wbr
    #
    wa
    #
    vj
    cA
    wrex
    #
    vk
    cr
    wral
    #
    vx
    cr
    wral
    wph
    @17
    @25
    vx
    cr
    wph
    @4
    cr
    wcel
    #
    wa
    #
    @16
    @24
    vk
    cr
    @27
    @15
    @23
    vj
    cA
    wph
    @26
    vj
    limsupub.j
    @26
    vj
    nfv
    nfan
    #
    @27
    @1
    cA
    wcel
    #
    @15
    @23
    wi
    @27
    @29
    wa
    #
    @15
    @23
    @30
    @15
    wa
    @2
    @22
    @30
    @2
    @9
    simprl
    @30
    @9
    @22
    @2
    @30
    @9
    wa
    #
    @4
    @3
    @31
    @26
    @4
    cxr
    wcel
    wph
    @26
    @29
    @9
    simpllr
    @4
    rexr
    syl
    wph
    @29
    @3
    cxr
    wcel
    #
    @26
    @9
    wph
    cA
    cxr
    @1
    cF
    limsupub.f
    ffvelrnda
    #
    ad4ant13
    @30
    @9
    simpr
    xrltled
    adantrl
    jca
    ex
    ex
    reximdai
    ralimdv
    ralimdva
    imp
    limsuppnfd
    wph
    @21
    wn
    @18
    wph
    @20
    cpnf
    limsupub.n
    neneqd
    adantr
    pm2.65da
    @14
    @17
    wn
    #
    vx
    cr
    wrex
    @19
    @13
    @34
    vx
    cr
    @13
    @16
    wn
    #
    vk
    cr
    wrex
    @34
    @12
    @35
    vk
    cr
    @12
    @15
    wn
    #
    vj
    cA
    wral
    @35
    @11
    @36
    vj
    cA
    @2
    @9
    imnan
    ralbii
    @15
    vj
    cA
    ralnex
    bitri
    rexbii
    @16
    vk
    cr
    rexnal
    bitri
    rexbii
    @17
    vx
    cr
    rexnal
    bitri
    sylibr
    wph
    @8
    @13
    vx
    cr
    @27
    @7
    @12
    vk
    cr
    @27
    @0
    cr
    wcel
    #
    wa
    #
    @6
    @11
    vj
    cA
    @27
    @37
    vj
    @28
    @37
    vj
    nfv
    nfan
    @38
    @29
    wa
    #
    @5
    @10
    @2
    @39
    @3
    @4
    wph
    @29
    @32
    @26
    @37
    @33
    ad4ant14
    @39
    @4
    wph
    @26
    @37
    @29
    simpllr
    rexrd
    xrlenltd
    imbi2d
    ralbida
    rexbidva
    rexbidva
    mpbird
end
