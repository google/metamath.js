include "weu.mm"
include "cio.mm"
include "cab.mm"
include "cuni.mm"
include "wss.mm"
include "wceq.mm"
include "iotauni.mm"
include "eqimss.mm"
include "syl.mm"
include "wn.mm"
include "c0.mm"
include "iotanul.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61i.mm"

theorem iotassuni
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let wps: wff ps
  let vy: setvar y


  assert |- ( iota x ph ) C_ U. { x | ph }

  proof
    wph
    vx
    weu
    #
    wph
    vx
    cio
    #
    wph
    vx
    cab
    cuni
    #
    wss
    #
    @0
    @1
    @2
    wceq
    @3
    wph
    vx
    iotauni
    @1
    @2
    eqimss
    syl
    @0
    wn
    @1
    c0
    @2
    wph
    vx
    iotanul
    @2
    0ss
    syl6eqss
    pm2.61i
end
