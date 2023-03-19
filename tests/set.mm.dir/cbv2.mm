include "wal.mm"
include "wb.mm"
include "nf5ri.mm"
include "alrimi.mm"
include "nf5rd.mm"
include "cbv2h.mm"
include "syl.mm"

theorem cbv2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume cbv2.1: |- F/ x ph
  assume cbv2.2: |- F/ y ph
  assume cbv2.3: |- ( ph -> F/ y ps )
  assume cbv2.4: |- ( ph -> F/ x ch )
  assume cbv2.5: |- ( ph -> ( x = y -> ( ps <-> ch ) ) )


  assert |- ( ph -> ( A. x ps <-> A. y ch ) )

  proof
    wph
    wph
    vy
    wal
    #
    vx
    wal
    wps
    vx
    wal
    wch
    vy
    wal
    wb
    wph
    @0
    vx
    cbv2.1
    wph
    vy
    cbv2.2
    nf5ri
    alrimi
    wph
    wps
    wch
    vx
    vy
    wph
    wps
    vy
    cbv2.3
    nf5rd
    wph
    wch
    vx
    cbv2.4
    nf5rd
    cbv2.5
    cbv2h
    syl
end
