include "wi.mm"
include "a2i.mm"
include "syl.mm"

theorem wl-mps
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume wl-mps.1: |- ( ph -> ( ps -> ch ) )
  assume wl-mps.2: |- ( ( ph -> ch ) -> th )


  assert |- ( ( ph -> ps ) -> th )

  proof
    wph
    wps
    wi
    wph
    wch
    wi
    wth
    wph
    wps
    wch
    wl-mps.1
    a2i
    wl-mps.2
    syl
end
