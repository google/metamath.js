include "wi.mm"
include "ax-1.mm"
include "syl.mm"

theorem a1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
