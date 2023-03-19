include "wrex.mm"
include "wreu.mm"
include "wrmo.mm"
include "wa.mm"
include "reu5.mm"
include "rexcom.mm"
include "nfcv.mm"
include "nfre1.mm"
include "nfrmo.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "rspe.mm"
include "ex.mm"
include "ralrimivw.mm"
include "rmoim.mm"
include "syl.mm"
include "impcom.mm"
include "rmo5.mm"
include "sylib.mm"
include "reximdai.mm"
include "syl5bi.mm"
include "sylbi.mm"

theorem 2reurex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k

  disjoint A y
  disjoint x y
  disjoint B x
  disjoint k x
  assert |- ( E! x e. A E. y e. B ph -> E. y e. B E! x e. A ph )

  proof
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wreu
    @0
    vx
    cA
    wrex
    #
    @0
    vx
    cA
    wrmo
    #
    wa
    wph
    vx
    cA
    wreu
    #
    vy
    cB
    wrex
    #
    @0
    vx
    cA
    reu5
    @2
    @1
    @4
    @1
    wph
    vx
    cA
    wrex
    #
    vy
    cB
    wrex
    @2
    @4
    wph
    vx
    vy
    cA
    cB
    rexcom
    @2
    @5
    @3
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
    @2
    vy
    cv
    cB
    wcel
    #
    @5
    @3
    wi
    #
    @2
    @6
    wa
    wph
    vx
    cA
    wrmo
    #
    @7
    @6
    @2
    @8
    @6
    wph
    @0
    wi
    #
    vx
    cA
    wral
    @2
    @8
    wi
    @6
    @9
    vx
    cA
    @6
    wph
    @0
    wph
    vy
    cB
    rspe
    ex
    ralrimivw
    wph
    @0
    vx
    cA
    rmoim
    syl
    impcom
    wph
    vx
    cA
    rmo5
    sylib
    ex
    reximdai
    syl5bi
    impcom
    sylbi
end
