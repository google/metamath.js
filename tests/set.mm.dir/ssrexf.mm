include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "nfss.mm"
include "ssel.mm"
include "anim1d.mm"
include "eximd.mm"
include "df-rex.mm"
include "3imtr4g.mm"

theorem ssrexf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ssrexf.1: |- F/_ x A
  assume ssrexf.2: |- F/_ x B


  assert |- ( A C_ B -> ( E. x e. A ph -> E. x e. B ph ) )

  proof
    cA
    cB
    wss
    #
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    wex
    @1
    cB
    wcel
    #
    wph
    wa
    #
    vx
    wex
    wph
    vx
    cA
    wrex
    wph
    vx
    cB
    wrex
    @0
    @3
    @5
    vx
    vx
    cA
    cB
    ssrexf.1
    ssrexf.2
    nfss
    @0
    @2
    @4
    wph
    cA
    cB
    @1
    ssel
    anim1d
    eximd
    wph
    vx
    cA
    df-rex
    wph
    vx
    cB
    df-rex
    3imtr4g
end
