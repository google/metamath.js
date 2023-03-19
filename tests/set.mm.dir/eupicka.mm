include "weu.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "nfeu1.mm"
include "nfe1.mm"
include "nfan.mm"
include "eupick.mm"
include "alrimi.mm"

theorem eupicka
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> A. x ( ph -> ps ) )

  proof
    wph
    vx
    weu
    #
    wph
    wps
    wa
    #
    vx
    wex
    #
    wa
    wph
    wps
    wi
    vx
    @0
    @2
    vx
    wph
    vx
    nfeu1
    @1
    vx
    nfe1
    nfan
    wph
    wps
    vx
    eupick
    alrimi
end
