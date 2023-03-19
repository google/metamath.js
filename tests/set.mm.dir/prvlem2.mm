include "cprvb.mm"
include "wi.mm"
include "prvlem1.mm"
include "ax-prv2.mm"
include "syl.mm"

theorem prvlem2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume prvlem2.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( Prv ph -> ( Prv ps -> Prv ch ) )

  proof
    wph
    cprvb
    wps
    wch
    wi
    #
    cprvb
    wps
    cprvb
    wch
    cprvb
    wi
    wph
    @0
    prvlem2.1
    prvlem1
    wps
    wch
    ax-prv2
    syl
end
