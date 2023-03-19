include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "walsc.mm"
include "wa.mm"
include "df-alsc.mm"
include "sylib.mm"
include "simpld.mm"

theorem alsc1d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  assume alsc1d.1: |- ( ph -> A! x e. A ps )


  assert |- ( ph -> A. x e. A ps )

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
    alsc1d.1
    wps
    vx
    cA
    df-alsc
    sylib
    simpld
end
