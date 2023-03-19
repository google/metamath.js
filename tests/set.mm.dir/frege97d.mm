include "ctcl.mm"
include "cfv.mm"
include "ccom.mm"
include "cima.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "trclfvlb.mm"
include "coss1.mm"
include "3syl.mm"
include "trclfvcotrg.mm"
include "syl6ss.mm"
include "imass1.mm"
include "syl.mm"
include "imaeq2d.mm"
include "imaco.mm"
include "syl6eqr.mm"
include "3sstr4d.mm"

theorem frege97d
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cU: class U
  assume frege97d.r: |- ( ph -> R e. _V )
  assume frege97d.a: |- ( ph -> A = ( ( t+ ` R ) " U ) )


  assert |- ( ph -> ( R " A ) C_ A )

  proof
    wph
    cR
    cR
    ctcl
    cfv
    #
    ccom
    #
    cU
    cima
    #
    @0
    cU
    cima
    #
    cR
    cA
    cima
    #
    cA
    wph
    @1
    @0
    wss
    @2
    @3
    wss
    wph
    @1
    @0
    @0
    ccom
    #
    @0
    wph
    cR
    cvv
    wcel
    cR
    @0
    wss
    @1
    @5
    wss
    frege97d.r
    cR
    cvv
    trclfvlb
    cR
    @0
    @0
    coss1
    3syl
    cR
    trclfvcotrg
    syl6ss
    @1
    @0
    cU
    imass1
    syl
    wph
    @4
    cR
    @3
    cima
    @2
    wph
    cA
    @3
    cR
    frege97d.a
    imaeq2d
    cR
    @0
    cU
    imaco
    syl6eqr
    frege97d.a
    3sstr4d
end
