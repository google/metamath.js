include "wi.mm"
include "bj-imim21.mm"
include "ax-mp.mm"

theorem bj-imim21i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bj-imim21i.1: |- ( ph -> ps )


  assert |- ( ( ch -> ( ps -> th ) ) -> ( ch -> ( ph -> th ) ) )

  proof
    wph
    wps
    wi
    wch
    wps
    wth
    wi
    wi
    wch
    wph
    wth
    wi
    wi
    wi
    bj-imim21i.1
    wph
    wps
    wch
    wth
    bj-imim21
    ax-mp
end
