include "crab.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "df-rab.mm"
include "hban.mm"
include "hbab.mm"
include "hbxfreq.mm"

theorem bnj1441
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume bnj1441.1: |- ( x e. A -> A. y x e. A )
  assume bnj1441.2: |- ( ph -> A. y ph )

  disjoint y z
  assert |- ( z e. { x e. A | ph } -> A. y z e. { x e. A | ph } )

  proof
    vy
    vz
    wph
    vx
    cA
    crab
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cab
    wph
    vx
    cA
    df-rab
    @1
    vy
    vx
    vz
    @0
    wph
    vy
    bnj1441.1
    bnj1441.2
    hban
    hbab
    hbxfreq
end
