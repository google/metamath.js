include "wb.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "ralbiim.mm"
include "ralbii.mm"
include "r19.26.mm"
include "bitri.mm"

theorem 2ralbiim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k


  assert |- ( A. x e. A A. y e. B ( ph <-> ps ) <-> ( A. x e. A A. y e. B ( ph -> ps ) /\ A. x e. A A. y e. B ( ps -> ph ) ) )

  proof
    wph
    wps
    wb
    vy
    cB
    wral
    #
    vx
    cA
    wral
    wph
    wps
    wi
    vy
    cB
    wral
    #
    wps
    wph
    wi
    vy
    cB
    wral
    #
    wa
    #
    vx
    cA
    wral
    @1
    vx
    cA
    wral
    @2
    vx
    cA
    wral
    wa
    @0
    @3
    vx
    cA
    wph
    wps
    vy
    cB
    ralbiim
    ralbii
    @1
    @2
    vx
    cA
    r19.26
    bitri
end
