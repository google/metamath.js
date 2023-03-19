include "wal.mm"
include "weq.mm"
include "wi.mm"
include "spw.mm"
include "ax12wlem.mm"
include "syl5.mm"

theorem ax12w
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ax12w.1: |- ( x = y -> ( ph <-> ps ) )
  assume ax12w.2: |- ( y = z -> ( ph <-> ch ) )

  disjoint y z
  disjoint ps x
  disjoint ph z
  disjoint ch y
  assert |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) )

  proof
    wph
    vy
    wal
    wph
    vx
    vy
    weq
    #
    @0
    wph
    wi
    vx
    wal
    wph
    wch
    vy
    vz
    ax12w.2
    spw
    wph
    wps
    vx
    vy
    ax12w.1
    ax12wlem
    syl5
end
