include "wo.mm"
include "wi.mm"
include "orc.mm"
include "olc.mm"
include "imim2i.mm"
include "jao.mm"
include "mpsyl.mm"

theorem bj-orim2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ch \/ ph ) -> ( ch \/ ps ) ) )

  proof
    wch
    wch
    wps
    wo
    #
    wi
    wph
    wps
    wi
    wph
    @0
    wi
    wch
    wph
    wo
    @0
    wi
    wch
    wps
    orc
    wps
    @0
    wph
    wps
    wch
    olc
    imim2i
    wch
    @0
    wph
    jao
    mpsyl
end
