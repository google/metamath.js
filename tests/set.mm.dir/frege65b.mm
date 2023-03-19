include "wi.mm"
include "wsb.mm"
include "wal.mm"
include "sbim.mm"
include "frege64b.mm"
include "sylbi.mm"
include "frege61b.mm"
include "ax-mp.mm"

theorem frege65b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( ph -> ps ) -> ( A. x ( ps -> ch ) -> ( [ y / x ] ph -> [ y / x ] ch ) ) )

  proof
    wph
    wps
    wi
    #
    vx
    vy
    wsb
    #
    wps
    wch
    wi
    vx
    wal
    wph
    vx
    vy
    wsb
    #
    wch
    vx
    vy
    wsb
    wi
    wi
    #
    wi
    @0
    vx
    wal
    @3
    wi
    @1
    @2
    wps
    vx
    vy
    wsb
    wi
    @3
    wph
    wps
    vx
    vy
    sbim
    wph
    wps
    wch
    vy
    vx
    vy
    frege64b
    sylbi
    @0
    @3
    vy
    vx
    frege61b
    ax-mp
end
