include "weu.mm"
include "cio.mm"
include "cab.mm"
include "cuni.mm"
include "c0.mm"
include "cif.mm"
include "wceq.mm"
include "iotauni.mm"
include "iftrue.mm"
include "eqtr4d.mm"
include "wn.mm"
include "iotanul.mm"
include "iffalse.mm"
include "pm2.61i.mm"

theorem dfiota4OLD
  let wph: wff ph
  let vx: setvar x


  assert |- ( iota x ph ) = if ( E! x ph , U. { x | ph } , (/) )

  proof
    wph
    vx
    weu
    #
    wph
    vx
    cio
    #
    @0
    wph
    vx
    cab
    cuni
    #
    c0
    cif
    #
    wceq
    @0
    @1
    @2
    @3
    wph
    vx
    iotauni
    @0
    @2
    c0
    iftrue
    eqtr4d
    @0
    wn
    @1
    c0
    @3
    wph
    vx
    iotanul
    @0
    @2
    c0
    iffalse
    eqtr4d
    pm2.61i
end
