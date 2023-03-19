include "wal.mm"
include "wi.mm"
include "ax-gen.mm"
include "hbimtg.mm"
include "mp2an.mm"

theorem hbimg
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  assume hbg.1: |- ( ph -> A. x ps )
  assume hbg.2: |- ( ch -> A. x th )


  assert |- ( ( ps -> ch ) -> A. x ( ph -> th ) )

  proof
    wph
    wps
    vx
    wal
    wi
    #
    vx
    wal
    wch
    wth
    vx
    wal
    wi
    wps
    wch
    wi
    wph
    wth
    wi
    vx
    wal
    wi
    @0
    vx
    hbg.1
    ax-gen
    hbg.2
    wph
    wch
    wps
    wth
    vx
    hbimtg
    mp2an
end
