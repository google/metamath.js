include "wi.mm"
include "ax-1.mm"
include "syl.mm"

theorem a1d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume a1d.1: |- ( ph -> ps )


  assert |- ( ph -> ( ch -> ps ) )

  proof
    wph
    wps
    wch
    wps
    wi
    a1d.1
    wps
    wch
    ax-1
    syl
end
