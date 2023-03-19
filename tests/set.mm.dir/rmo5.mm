include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wex.mm"
include "weu.mm"
include "wi.mm"
include "wrmo.mm"
include "wrex.mm"
include "wreu.mm"
include "df-mo.mm"
include "df-rmo.mm"
include "df-rex.mm"
include "df-reu.mm"
include "imbi12i.mm"
include "3bitr4i.mm"

theorem rmo5
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( E* x e. A ph <-> ( E. x e. A ph -> E! x e. A ph ) )

  proof
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    vx
    wmo
    @0
    vx
    wex
    #
    @0
    vx
    weu
    #
    wi
    wph
    vx
    cA
    wrmo
    wph
    vx
    cA
    wrex
    #
    wph
    vx
    cA
    wreu
    #
    wi
    @0
    vx
    df-mo
    wph
    vx
    cA
    df-rmo
    @3
    @1
    @4
    @2
    wph
    vx
    cA
    df-rex
    wph
    vx
    cA
    df-reu
    imbi12i
    3bitr4i
end
