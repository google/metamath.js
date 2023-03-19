include "wi.mm"
include "wo.mm"
include "orel2.mm"
include "ax-1.mm"
include "ja.mm"
include "orim1d.mm"

theorem pm2.74
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ps -> ph ) -> ( ( ( ph \/ ps ) \/ ch ) -> ( ph \/ ch ) ) )

  proof
    wps
    wph
    wi
    wph
    wps
    wo
    #
    wph
    wch
    wps
    wph
    @0
    wph
    wi
    wps
    wph
    orel2
    wph
    @0
    ax-1
    ja
    orim1d
end
