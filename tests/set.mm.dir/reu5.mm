include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weu.mm"
include "wex.mm"
include "wmo.mm"
include "wreu.mm"
include "wrex.mm"
include "wrmo.mm"
include "eu5.mm"
include "df-reu.mm"
include "df-rex.mm"
include "df-rmo.mm"
include "anbi12i.mm"
include "3bitr4i.mm"

theorem reu5
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( E! x e. A ph <-> ( E. x e. A ph /\ E* x e. A ph ) )

  proof
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    vx
    weu
    @0
    vx
    wex
    #
    @0
    vx
    wmo
    #
    wa
    wph
    vx
    cA
    wreu
    wph
    vx
    cA
    wrex
    #
    wph
    vx
    cA
    wrmo
    #
    wa
    @0
    vx
    eu5
    wph
    vx
    cA
    df-reu
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
    df-rmo
    anbi12i
    3bitr4i
end
