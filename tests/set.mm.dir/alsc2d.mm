include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "walsc.mm"
include "wa.mm"
include "df-alsc.mm"
include "sylib.mm"
include "simprd.mm"

theorem alsc2d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  assume alsc2d.1: |- ( ph -> A! x e. A ps )


  assert |- ( ph -> E. x x e. A )

  proof
    wph
    wps
    vx
    cA
    wral
    #
    vx
    cv
    cA
    wcel
    vx
    wex
    #
    wph
    wps
    vx
    cA
    walsc
    @0
    @1
    wa
    alsc2d.1
    wps
    vx
    cA
    df-alsc
    sylib
    simprd
end
