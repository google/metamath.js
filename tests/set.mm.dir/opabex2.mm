include "copab.mm"
include "cxp.mm"
include "cvv.mm"
include "wcel.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "opabssxpd.mm"
include "ssexd.mm"

theorem opabex2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume opabex2.1: |- ( ph -> A e. V )
  assume opabex2.2: |- ( ph -> B e. W )
  assume opabex2.3: |- ( ( ph /\ ps ) -> x e. A )
  assume opabex2.4: |- ( ( ph /\ ps ) -> y e. B )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> { <. x , y >. | ps } e. _V )

  proof
    wph
    wps
    vx
    vy
    copab
    cA
    cB
    cxp
    #
    cvv
    wph
    cA
    cV
    wcel
    cB
    cW
    wcel
    @0
    cvv
    wcel
    opabex2.1
    opabex2.2
    cA
    cB
    cV
    cW
    xpexg
    syl2anc
    wph
    wps
    vx
    vy
    cA
    cB
    opabex2.3
    opabex2.4
    opabssxpd
    ssexd
end
