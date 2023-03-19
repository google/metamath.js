include "wi.mm"
include "wo.mm"
include "orc.mm"
include "imim2i.mm"
include "olc.mm"
include "jaao.mm"

theorem pm3.48
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph -> ps ) /\ ( ch -> th ) ) -> ( ( ph \/ ch ) -> ( ps \/ th ) ) )

  proof
    wph
    wps
    wi
    wph
    wps
    wth
    wo
    #
    wch
    wth
    wi
    wch
    wps
    @0
    wph
    wps
    wth
    orc
    imim2i
    wth
    @0
    wch
    wth
    wps
    olc
    imim2i
    jaao
end
