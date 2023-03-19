include "weq.mm"
include "wa.mm"
include "wex.mm"
include "biimpa.mm"
include "exlimi.mm"
include "wi.mm"
include "wal.mm"
include "equsal.mm"
include "equs4.mm"
include "sylbir.mm"
include "impbii.mm"

theorem equsex
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume equsal.1: |- F/ x ps
  assume equsal.2: |- ( x = y -> ( ph <-> ps ) )


  assert |- ( E. x ( x = y /\ ph ) <-> ps )

  proof
    vx
    vy
    weq
    #
    wph
    wa
    #
    vx
    wex
    #
    wps
    @1
    wps
    vx
    equsal.1
    @0
    wph
    wps
    equsal.2
    biimpa
    exlimi
    wps
    @0
    wph
    wi
    vx
    wal
    @2
    wph
    wps
    vx
    vy
    equsal.1
    equsal.2
    equsal
    wph
    vx
    vy
    equs4
    sylbir
    impbii
end
