include "weu.mm"
include "cab.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wex.mm"
include "cuni.mm"
include "cint.mm"
include "euabsn2.mm"
include "uniintsn.mm"
include "bitr4i.mm"

theorem uniintab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( E! x ph <-> U. { x | ph } = |^| { x | ph } )

  proof
    wph
    vx
    weu
    wph
    vx
    cab
    #
    vy
    cv
    csn
    wceq
    vy
    wex
    @0
    cuni
    @0
    cint
    wceq
    wph
    vx
    vy
    euabsn2
    vy
    @0
    uniintsn
    bitr4i
end
