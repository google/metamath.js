include "ccnv.mm"
include "cmnf.mm"
include "cioo.mm"
include "co.mm"
include "cima.mm"
include "cico.mm"
include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "cr.mm"
include "cin.mm"
include "wfun.mm"
include "crn.mm"
include "wss.mm"
include "wceq.mm"
include "ffund.mm"
include "frnd.mm"
include "fimacnvinrn2.mm"
include "syl2anc.mm"
include "icomnfinre.mm"
include "imaeq2d.mm"
include "eqtr2d.mm"
include "frexr.mm"
include "preimaicomnf.mm"
include "eqtrd.mm"

theorem preimaioomnf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  assume preimaioomnf.1: |- ( ph -> F : A --> RR )
  assume preimaioomnf.2: |- ( ph -> B e. RR* )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( `' F " ( -oo (,) B ) ) = { x e. A | ( F ` x ) < B } )

  proof
    wph
    cF
    ccnv
    #
    cmnf
    cB
    cioo
    co
    #
    cima
    #
    @0
    cmnf
    cB
    cico
    co
    #
    cima
    #
    vx
    cv
    cF
    cfv
    cB
    clt
    wbr
    vx
    cA
    crab
    wph
    @4
    @0
    @3
    cr
    cin
    #
    cima
    #
    @2
    wph
    cF
    wfun
    cF
    crn
    cr
    wss
    @4
    @6
    wceq
    wph
    cA
    cr
    cF
    preimaioomnf.1
    ffund
    wph
    cA
    cr
    cF
    preimaioomnf.1
    frnd
    @3
    cr
    cF
    fimacnvinrn2
    syl2anc
    wph
    @5
    @1
    @0
    wph
    cB
    preimaioomnf.2
    icomnfinre
    imaeq2d
    eqtr2d
    wph
    vx
    cA
    cB
    cF
    wph
    cA
    cF
    preimaioomnf.1
    frexr
    preimaioomnf.2
    preimaicomnf
    eqtrd
end
