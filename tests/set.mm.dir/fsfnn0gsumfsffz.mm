include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "cn0.mm"
include "wral.mm"
include "cgsu.mm"
include "co.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "cres.mm"
include "oveq2i.mm"
include "cvv.mm"
include "ccmn.mm"
include "wcel.mm"
include "adantr.mm"
include "nn0ex.mm"
include "a1i.mm"
include "wf.mm"
include "cmap.mm"
include "elmapi.mm"
include "syl.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "simpr.mm"
include "suppssfz.mm"
include "csupp.mm"
include "wss.mm"
include "cfsupp.mm"
include "wfun.mm"
include "w3a.mm"
include "cfn.mm"
include "elmapfun.mm"
include "3jca.mm"
include "fzfid.mm"
include "anim1i.mm"
include "suppssfifsupp.mm"
include "syl2anc.mm"
include "syldan.mm"
include "gsumres.mm"
include "syl5req.mm"
include "ex.mm"

theorem fsfnn0gsumfsffz
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let c.0: class .0.
  assume nn0gsumfz.b: |- B = ( Base ` G )
  assume nn0gsumfz.0: |- .0. = ( 0g ` G )
  assume nn0gsumfz.g: |- ( ph -> G e. CMnd )
  assume nn0gsumfz.f: |- ( ph -> F e. ( B ^m NN0 ) )
  assume fsfnn0gsumfsffz.s: |- ( ph -> S e. NN0 )
  assume fsfnn0gsumfsffz.h: |- H = ( F |` ( 0 ... S ) )

  disjoint F x
  disjoint S x
  disjoint .0. x
  assert |- ( ph -> ( A. x e. NN0 ( S < x -> ( F ` x ) = .0. ) -> ( G gsum F ) = ( G gsum H ) ) )

  proof
    wph
    cS
    vx
    cv
    #
    clt
    wbr
    @0
    cF
    cfv
    c.0
    wceq
    wi
    vx
    cn0
    wral
    #
    cG
    cF
    cgsu
    co
    #
    cG
    cH
    cgsu
    co
    #
    wceq
    wph
    @1
    wa
    #
    @3
    cG
    cF
    cc0
    cS
    cfz
    co
    #
    cres
    #
    cgsu
    co
    @2
    cH
    @6
    cG
    cgsu
    fsfnn0gsumfsffz.h
    oveq2i
    @4
    cn0
    cB
    cF
    cG
    cvv
    @5
    c.0
    nn0gsumfz.b
    nn0gsumfz.0
    wph
    cG
    ccmn
    wcel
    @1
    nn0gsumfz.g
    adantr
    cn0
    cvv
    wcel
    @4
    nn0ex
    a1i
    wph
    cn0
    cB
    cF
    wf
    #
    @1
    wph
    cF
    cB
    cn0
    cmap
    co
    #
    wcel
    #
    @7
    nn0gsumfz.f
    cF
    cB
    cn0
    elmapi
    syl
    adantr
    @4
    vx
    cB
    cS
    cF
    cvv
    c.0
    c.0
    cvv
    wcel
    #
    @4
    c.0
    cG
    c0g
    cfv
    cvv
    nn0gsumfz.0
    cG
    c0g
    fvex
    eqeltri
    #
    a1i
    wph
    @9
    @1
    nn0gsumfz.f
    adantr
    wph
    cS
    cn0
    wcel
    @1
    fsfnn0gsumfsffz.s
    adantr
    wph
    @1
    simpr
    suppssfz
    #
    wph
    @1
    cF
    c.0
    csupp
    co
    @5
    wss
    #
    cF
    c.0
    cfsupp
    wbr
    #
    @12
    wph
    @13
    wa
    @9
    cF
    wfun
    #
    @10
    w3a
    #
    @5
    cfn
    wcel
    #
    @13
    wa
    @14
    wph
    @16
    @13
    wph
    @9
    @15
    @10
    nn0gsumfz.f
    wph
    @9
    @15
    nn0gsumfz.f
    cF
    cB
    cn0
    elmapfun
    syl
    @10
    wph
    @11
    a1i
    3jca
    adantr
    wph
    @17
    @13
    wph
    cc0
    cS
    fzfid
    anim1i
    @5
    cF
    @8
    cvv
    c.0
    suppssfifsupp
    syl2anc
    syldan
    gsumres
    syl5req
    ex
end
