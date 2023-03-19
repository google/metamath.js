include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "nfv.mm"
include "nfan.mm"
include "wb.mm"
include "anassrs.mm"
include "ralbida.mm"

theorem 2ralbida
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume 2ralbida.1: |- F/ x ph
  assume 2ralbida.2: |- F/ y ph
  assume 2ralbida.3: |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps <-> ch ) )

  disjoint x y
  disjoint A y
  assert |- ( ph -> ( A. x e. A A. y e. B ps <-> A. x e. A A. y e. B ch ) )

  proof
    wph
    wps
    vy
    cB
    wral
    wch
    vy
    cB
    wral
    vx
    cA
    2ralbida.1
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    wps
    wch
    vy
    cB
    wph
    @0
    vy
    2ralbida.2
    @0
    vy
    nfv
    nfan
    wph
    @0
    vy
    cv
    cB
    wcel
    wps
    wch
    wb
    2ralbida.3
    anassrs
    ralbida
    ralbida
end
