include "cv.mm"
include "wcel.mm"
include "cab.mm"
include "eleq2d.mm"
include "abid.mm"
include "syl6bb.mm"

theorem abeq2d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume abeq2d.1: |- ( ph -> A = { x | ps } )


  assert |- ( ph -> ( x e. A <-> ps ) )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    @0
    wps
    vx
    cab
    #
    wcel
    wps
    wph
    cA
    @1
    @0
    abeq2d.1
    eleq2d
    wps
    vx
    abid
    syl6bb
end
