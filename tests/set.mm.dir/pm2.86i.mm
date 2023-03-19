include "wi.mm"
include "ax-1.mm"
include "syl11.mm"

theorem pm2.86i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm2.86i.1: |- ( ( ph -> ps ) -> ( ph -> ch ) )


  assert |- ( ph -> ( ps -> ch ) )

  proof
    wph
    wps
    wi
    wph
    wch
    wps
    pm2.86i.1
    wps
    wph
    ax-1
    syl11
end
