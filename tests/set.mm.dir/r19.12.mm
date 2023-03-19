include "wral.mm"
include "wrex.mm"
include "nfcv.mm"
include "nfra1.mm"
include "nfrex.mm"
include "cv.mm"
include "wcel.mm"
include "ax-1.mm"
include "ralrimi.mm"
include "rsp.mm"
include "com12.mm"
include "reximdv.mm"
include "ralimia.mm"
include "syl.mm"

theorem r19.12
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A y
  disjoint B x
  assert |- ( E. x e. A A. y e. B ph -> A. y e. B E. x e. A ph )

  proof
    wph
    vy
    cB
    wral
    #
    vx
    cA
    wrex
    #
    @1
    vy
    cB
    wral
    wph
    vx
    cA
    wrex
    #
    vy
    cB
    wral
    @1
    @1
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
    nfra1
    nfrex
    @1
    vy
    cv
    cB
    wcel
    #
    ax-1
    ralrimi
    @1
    @2
    vy
    cB
    @3
    @0
    wph
    vx
    cA
    @0
    @3
    wph
    wph
    vy
    cB
    rsp
    com12
    reximdv
    ralimia
    syl
end
