include "wi.mm"
include "wal.mm"
include "wsb.mm"
include "frege65b.mm"
include "ax-frege8.mm"
include "ax-mp.mm"

theorem frege66b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( ph -> ps ) -> ( A. x ( ch -> ph ) -> ( [ y / x ] ch -> [ y / x ] ps ) ) )

  proof
    wch
    wph
    wi
    vx
    wal
    #
    wph
    wps
    wi
    vx
    wal
    #
    wch
    vx
    vy
    wsb
    wps
    vx
    vy
    wsb
    wi
    #
    wi
    wi
    @1
    @0
    @2
    wi
    wi
    wch
    wph
    wps
    vx
    vy
    frege65b
    @0
    @1
    @2
    ax-frege8
    ax-mp
end
