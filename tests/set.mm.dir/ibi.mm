include "biimpd.mm"
include "pm2.43i.mm"

theorem ibi
  let wph: wff ph
  let wps: wff ps
  assume ibi.1: |- ( ph -> ( ph <-> ps ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wph
    wph
    wps
    ibi.1
    biimpd
    pm2.43i
end
