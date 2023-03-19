include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "wi.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "ex.mm"
include "3syl.mm"
include "ralrimiv.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wral.mm"
include "weq.mm"
include "breq2.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "gsummptnn0fzv.mm"

theorem gsummptnn0fzfv
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let c.0: class .0.
  assume gsummptnn0fzfv.b: |- B = ( Base ` G )
  assume gsummptnn0fzfv.0: |- .0. = ( 0g ` G )
  assume gsummptnn0fzfv.g: |- ( ph -> G e. CMnd )
  assume gsummptnn0fzfv.f: |- ( ph -> F e. ( B ^m NN0 ) )
  assume gsummptnn0fzfv.s: |- ( ph -> S e. NN0 )
  assume gsummptnn0fzfv.u: |- ( ph -> A. x e. NN0 ( S < x -> ( F ` x ) = .0. ) )

  disjoint B k
  disjoint F k
  disjoint F x
  disjoint k x
  disjoint S k
  disjoint S x
  disjoint .0. k
  disjoint .0. x
  disjoint k ph
  disjoint ph x
  assert |- ( ph -> ( G gsum ( k e. NN0 |-> ( F ` k ) ) ) = ( G gsum ( k e. ( 0 ... S ) |-> ( F ` k ) ) ) )

  proof
    wph
    cB
    vk
    cv
    #
    cF
    cfv
    #
    cS
    vk
    cG
    c.0
    gsummptnn0fzfv.b
    gsummptnn0fzfv.0
    gsummptnn0fzfv.g
    wph
    @1
    cB
    wcel
    #
    vk
    cn0
    wph
    cF
    cB
    cn0
    cmap
    co
    wcel
    cn0
    cB
    cF
    wf
    #
    @0
    cn0
    wcel
    #
    @2
    wi
    gsummptnn0fzfv.f
    cF
    cB
    cn0
    elmapi
    @3
    @4
    @2
    cn0
    cB
    @0
    cF
    ffvelrn
    ex
    3syl
    ralrimiv
    gsummptnn0fzfv.s
    wph
    cS
    vx
    cv
    #
    clt
    wbr
    #
    @5
    cF
    cfv
    #
    c.0
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    cS
    @0
    clt
    wbr
    #
    @1
    c.0
    wceq
    #
    wi
    #
    vk
    cn0
    wral
    gsummptnn0fzfv.u
    @9
    @12
    vx
    vk
    cn0
    vx
    vk
    weq
    #
    @6
    @10
    @8
    @11
    @5
    @0
    cS
    clt
    breq2
    @13
    @7
    @1
    c.0
    @5
    @0
    cF
    fveq2
    eqeq1d
    imbi12d
    cbvralv
    sylib
    gsummptnn0fzv
end
