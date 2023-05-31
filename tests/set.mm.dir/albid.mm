include "nf5ri.mm"
include "albidh.mm"

theorem albid
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume albid.1: |- F/ x ph
  assume albid.2: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( A. x ps <-> A. x ch ) )

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
    albidh
end
