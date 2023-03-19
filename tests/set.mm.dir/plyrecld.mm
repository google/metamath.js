include "cr.mm"
include "cres.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvres.mm"
include "syl.mm"
include "cply.mm"
include "wf.mm"
include "plyreres.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"

theorem plyrecld
  let wph: wff ph
  let cF: class F
  let cX: class X
  assume plyrecld.1: |- ( ph -> F e. ( Poly ` RR ) )
  assume plyrecld.2: |- ( ph -> X e. RR )


  assert |- ( ph -> ( F ` X ) e. RR )

  proof
    wph
    cX
    cF
    cr
    cres
    #
    cfv
    #
    cX
    cF
    cfv
    #
    cr
    wph
    cX
    cr
    wcel
    @1
    @2
    wceq
    plyrecld.2
    cX
    cr
    cF
    fvres
    syl
    wph
    cr
    cr
    cX
    @0
    wph
    cF
    cr
    cply
    cfv
    wcel
    cr
    cr
    @0
    wf
    plyrecld.1
    cF
    plyreres
    syl
    plyrecld.2
    ffvelrnd
    eqeltrrd
end
