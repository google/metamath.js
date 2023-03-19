include "nf5ri.mm"
include "exbidh.mm"

theorem exbid
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume albid.1: |- F/ x ph
  assume albid.2: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( E. x ps <-> E. x ch ) )

  proof
    wph
    wps
    wch
    vx
    wph
    vx
    albid.1
    nf5ri
    albid.2
    exbidh
end
