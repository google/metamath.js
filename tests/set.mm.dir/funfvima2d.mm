include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "cima.mm"
include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "wi.mm"
include "wf.mm"
include "ffun.mm"
include "syl.mm"
include "ssid.mm"
include "a1i.mm"
include "wceq.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funfvima2.mm"
include "syl2anc.mm"
include "imp.mm"

theorem funfvima2d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume funfvima2d.1: |- ( ph -> F : A --> B )


  assert |- ( ( ph /\ x e. A ) -> ( F ` x ) e. ( F " A ) )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cF
    cfv
    cF
    cA
    cima
    wcel
    #
    wph
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wss
    @1
    @2
    wi
    wph
    cA
    cB
    cF
    wf
    #
    @3
    funfvima2d.1
    cA
    cB
    cF
    ffun
    syl
    wph
    cA
    cA
    @4
    cA
    cA
    wss
    wph
    cA
    ssid
    a1i
    wph
    @5
    @4
    cA
    wceq
    funfvima2d.1
    cA
    cB
    cF
    fdm
    syl
    sseqtr4d
    cA
    @0
    cF
    funfvima2
    syl2anc
    imp
end
