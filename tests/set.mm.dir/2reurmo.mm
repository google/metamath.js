include "wreu.mm"
include "wrmo.mm"
include "wi.mm"
include "reuimrmo.mm"
include "cv.mm"
include "wcel.mm"
include "reurmo.mm"
include "a1i.mm"
include "mprg.mm"

theorem 2reurmo
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
  assert |- ( E! x e. A E* y e. B ph -> E* x e. A E! y e. B ph )

  proof
    wph
    vy
    cB
    wreu
    #
    wph
    vy
    cB
    wrmo
    #
    wi
    #
    @1
    vx
    cA
    wreu
    @0
    vx
    cA
    wrmo
    wi
    vx
    cA
    @0
    @1
    vx
    cA
    reuimrmo
    @2
    vx
    cv
    cA
    wcel
    wph
    vy
    cB
    reurmo
    a1i
    mprg
end
