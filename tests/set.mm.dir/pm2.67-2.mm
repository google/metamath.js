include "wo.mm"
include "orc.mm"
include "imim1i.mm"

theorem pm2.67-2
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch


  assert |- ( ( ( ph \/ ch ) -> ps ) -> ( ph -> ps ) )

  proof
    wph
    wph
    wch
    wo
    wps
    wph
    wch
    orc
    imim1i
end
