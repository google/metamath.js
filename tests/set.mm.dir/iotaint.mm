include "weu.mm"
include "cio.mm"
include "cab.mm"
include "cuni.mm"
include "cint.mm"
include "iotauni.mm"
include "wceq.mm"
include "uniintab.mm"
include "biimpi.mm"
include "eqtrd.mm"

theorem iotaint
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let wps: wff ps
  let vy: setvar y


  assert |- ( E! x ph -> ( iota x ph ) = |^| { x | ph } )

  proof
    wph
    vx
    weu
    #
    wph
    vx
    cio
    wph
    vx
    cab
    #
    cuni
    #
    @1
    cint
    #
    wph
    vx
    iotauni
    @0
    @2
    @3
    wceq
    wph
    vx
    uniintab
    biimpi
    eqtrd
end
