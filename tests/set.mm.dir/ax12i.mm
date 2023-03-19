include "weq.mm"
include "wi.mm"
include "wal.mm"
include "biimprcd.mm"
include "alrimih.mm"
include "syl6bi.mm"

theorem ax12i
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume ax12i.1: |- ( x = y -> ( ph <-> ps ) )
  assume ax12i.2: |- ( ps -> A. x ps )


  assert |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) )

  proof
    vx
    vy
    weq
    #
    wph
    wps
    @0
    wph
    wi
    #
    vx
    wal
    ax12i.1
    wps
    @1
    vx
    ax12i.2
    @0
    wph
    wps
    ax12i.1
    biimprcd
    alrimih
    syl6bi
end
