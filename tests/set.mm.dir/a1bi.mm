include "wi.mm"
include "wb.mm"
include "biimt.mm"
include "ax-mp.mm"

theorem a1bi
  param wph: wff ph
  param wps: wff ps
  assume a1bi.1: |- ph


  assert |- ( ps <-> ( ph -> ps ) )

  proof
    wph
    wps
    wph
    wps
    wi
    wb
    a1bi.1
    wph
    wps
    biimt
    ax-mp
end
