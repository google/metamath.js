include "wsb.mm"
include "wex.mm"
include "sb8e.mm"
include "sylib.mm"
include "cv.mm"
include "wsbc.mm"
include "sbsbc.mm"
include "bitri.mm"
include "sylanb.mm"
include "exlimddvf.mm"

theorem exlimddvfi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wet: wff et
  let vx: setvar x
  let vy: setvar y
  assume exlimddvfi.1: |- ( ph -> E. x th )
  assume exlimddvfi.2: |- F/ y th
  assume exlimddvfi.3: |- F/ y ps
  assume exlimddvfi.4: |- ( [. y / x ]. th <-> et )
  assume exlimddvfi.5: |- ( ( et /\ ps ) -> ch )
  assume exlimddvfi.6: |- F/ y ch


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    wth
    vx
    vy
    wsb
    #
    vy
    wph
    wth
    vx
    wex
    @0
    vy
    wex
    exlimddvfi.1
    wth
    vx
    vy
    exlimddvfi.2
    sb8e
    sylib
    exlimddvfi.3
    @0
    wet
    wps
    wch
    @0
    wth
    vx
    vy
    cv
    wsbc
    wet
    wth
    vx
    vy
    sbsbc
    exlimddvfi.4
    bitri
    exlimddvfi.5
    sylanb
    exlimddvfi.6
    exlimddvf
end
