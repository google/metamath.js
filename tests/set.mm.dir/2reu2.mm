include "wrex.mm"
include "wreu.mm"
include "wrmo.mm"
include "wral.mm"
include "wi.mm"
include "reurmo.mm"
include "2rmorex.mm"
include "wa.mm"
include "2reu1.mm"
include "simpl.mm"
include "syl6bi.mm"
include "3syl.mm"
include "2rexreu.mm"
include "expcom.mm"
include "impbid.mm"

theorem 2reu2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint k x
  assert |- ( E! y e. B E. x e. A ph -> ( E! x e. A E! y e. B ph <-> E! x e. A E. y e. B ph ) )

  proof
    wph
    vx
    cA
    wrex
    #
    vy
    cB
    wreu
    #
    wph
    vy
    cB
    wreu
    vx
    cA
    wreu
    #
    wph
    vy
    cB
    wrex
    vx
    cA
    wreu
    #
    @1
    @0
    vy
    cB
    wrmo
    wph
    vy
    cB
    wrmo
    vx
    cA
    wral
    #
    @2
    @3
    wi
    @0
    vy
    cB
    reurmo
    wph
    vy
    vx
    cB
    cA
    2rmorex
    @4
    @2
    @3
    @1
    wa
    @3
    wph
    vx
    vy
    cA
    cB
    2reu1
    @3
    @1
    simpl
    syl6bi
    3syl
    @3
    @1
    @2
    wph
    vx
    vy
    cA
    cB
    2rexreu
    expcom
    impbid
end
