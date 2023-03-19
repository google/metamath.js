include "wi.mm"
include "wal.mm"
include "bi2.04.mm"
include "albii.mm"
include "19.21v.mm"
include "bitri.mm"

theorem pm10.542
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x

  disjoint ch x
  assert |- ( A. x ( ph -> ( ch -> ps ) ) <-> ( ch -> A. x ( ph -> ps ) ) )

  proof
    wph
    wch
    wps
    wi
    wi
    #
    vx
    wal
    wch
    wph
    wps
    wi
    #
    wi
    #
    vx
    wal
    wch
    @1
    vx
    wal
    wi
    @0
    @2
    vx
    wph
    wch
    wps
    bi2.04
    albii
    wch
    @1
    vx
    19.21v
    bitri
end
