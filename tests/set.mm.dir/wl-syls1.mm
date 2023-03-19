include "wi.mm"
include "a1i.mm"
include "wl-mps.mm"

theorem wl-syls1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume wl-syls1.1: |- ( ps -> ch )
  assume wl-syls1.2: |- ( ( ph -> ch ) -> th )


  assert |- ( ( ph -> ps ) -> th )

  proof
    wph
    wps
    wch
    wth
    wps
    wch
    wi
    wph
    wl-syls1.1
    a1i
    wl-syls1.2
    wl-mps
end
