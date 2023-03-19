include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wrmo.mm"
include "wi.mm"
include "wal.mm"
include "dfss2f.mm"
include "biimpi.mm"
include "pm3.45.mm"
include "alimi.mm"
include "moim.mm"
include "3syl.mm"
include "df-rmo.mm"
include "3imtr4g.mm"

theorem ssrmo
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ssrmo.1: |- F/_ x A
  assume ssrmo.2: |- F/_ x B


  assert |- ( A C_ B -> ( E* x e. B ph -> E* x e. A ph ) )

  proof
    cA
    cB
    wss
    #
    vx
    cv
    #
    cB
    wcel
    #
    wph
    wa
    #
    vx
    wmo
    #
    @1
    cA
    wcel
    #
    wph
    wa
    #
    vx
    wmo
    #
    wph
    vx
    cB
    wrmo
    wph
    vx
    cA
    wrmo
    @0
    @5
    @2
    wi
    #
    vx
    wal
    #
    @6
    @3
    wi
    #
    vx
    wal
    @4
    @7
    wi
    @0
    @9
    vx
    cA
    cB
    ssrmo.1
    ssrmo.2
    dfss2f
    biimpi
    @8
    @10
    vx
    @5
    @2
    wph
    pm3.45
    alimi
    @6
    @3
    vx
    moim
    3syl
    wph
    vx
    cB
    df-rmo
    wph
    vx
    cA
    df-rmo
    3imtr4g
end
