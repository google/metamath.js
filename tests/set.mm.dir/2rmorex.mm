include "wrex.mm"
include "wrmo.mm"
include "nfcv.mm"
include "nfre1.mm"
include "nfrmo.mm"
include "wi.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "rmoim.mm"
include "rspe.mm"
include "ex.mm"
include "ralrimivw.mm"
include "syl11.mm"
include "ralrimi.mm"

theorem 2rmorex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint A y
  disjoint B x
  disjoint x y
  assert |- ( E* x e. A E. y e. B ph -> A. y e. B E* x e. A ph )

  proof
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wrmo
    #
    wph
    vx
    cA
    wrmo
    #
    vy
    cB
    @0
    vy
    vx
    cA
    vy
    cA
    nfcv
    wph
    vy
    cB
    nfre1
    nfrmo
    wph
    @0
    wi
    #
    vx
    cA
    wral
    @1
    @2
    vy
    cv
    cB
    wcel
    #
    wph
    @0
    vx
    cA
    rmoim
    @4
    @3
    vx
    cA
    @4
    wph
    @0
    wph
    vy
    cB
    rspe
    ex
    ralrimivw
    syl11
    ralrimi
end
