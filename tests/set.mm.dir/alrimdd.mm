include "wal.mm"
include "nf5rd.mm"
include "alimd.mm"
include "syld.mm"

theorem alrimdd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume alrimdd.1: |- F/ x ph
  assume alrimdd.2: |- ( ph -> F/ x ps )
  assume alrimdd.3: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ps -> A. x ch ) )

  proof
    wph
    wps
    wps
    vx
    wal
    wch
    vx
    wal
    wph
    wps
    vx
    alrimdd.2
    nf5rd
    wph
    wps
    wch
    vx
    alrimdd.1
    alrimdd.3
    alimd
    syld
end
