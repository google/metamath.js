include "wi.mm"
include "wal.mm"
include "wsb.mm"
include "ax-frege58b.mm"
include "sbim.mm"
include "imbi2i.mm"
include "bitri.mm"
include "sylib.mm"
include "frege12.mm"
include "ax-mp.mm"

theorem frege60b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( ph -> ( ps -> ch ) ) -> ( [ y / x ] ps -> ( [ y / x ] ph -> [ y / x ] ch ) ) )

  proof
    wph
    wps
    wch
    wi
    #
    wi
    #
    vx
    wal
    #
    wph
    vx
    vy
    wsb
    #
    wps
    vx
    vy
    wsb
    #
    wch
    vx
    vy
    wsb
    #
    wi
    #
    wi
    #
    wi
    @2
    @4
    @3
    @5
    wi
    wi
    wi
    @2
    @1
    vx
    vy
    wsb
    #
    @7
    @1
    vx
    vy
    ax-frege58b
    @8
    @3
    @0
    vx
    vy
    wsb
    #
    wi
    @7
    wph
    @0
    vx
    vy
    sbim
    @9
    @6
    @3
    wps
    wch
    vx
    vy
    sbim
    imbi2i
    bitri
    sylib
    @2
    @3
    @4
    @5
    frege12
    ax-mp
end
