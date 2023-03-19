include "wa.mm"
include "wex.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "df-an.mm"
include "2exbii.mm"
include "2nalexn.mm"
include "bitr4i.mm"

theorem pm11.52
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( E. x E. y ( ph /\ ps ) <-> -. A. x A. y ( ph -> -. ps ) )

  proof
    wph
    wps
    wa
    #
    vy
    wex
    vx
    wex
    wph
    wps
    wn
    wi
    #
    wn
    #
    vy
    wex
    vx
    wex
    @1
    vy
    wal
    vx
    wal
    wn
    @0
    @2
    vx
    vy
    wph
    wps
    df-an
    2exbii
    @1
    vx
    vy
    2nalexn
    bitr4i
end
