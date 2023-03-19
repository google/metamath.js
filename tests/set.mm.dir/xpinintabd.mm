include "cxp.mm"
include "inintabd.mm"

theorem xpinintabd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let cB: class B
  assume xpinintabd.x: |- ( ph -> E. x ps )

  disjoint ps w
  disjoint w x
  disjoint A w
  disjoint A x
  disjoint B w
  disjoint B x
  assert |- ( ph -> ( ( A X. B ) i^i |^| { x | ps } ) = |^| { w e. ~P ( A X. B ) | E. x ( w = ( ( A X. B ) i^i x ) /\ ps ) } )

  proof
    wph
    wps
    vx
    vw
    cA
    cB
    cxp
    xpinintabd.x
    inintabd
end
