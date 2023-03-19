include "wi.mm"
include "cprvb.mm"
include "ax-prv1.mm"
include "ax-prv2.mm"
include "ax-mp.mm"

theorem prvlem1
  let wph: wff ph
  let wps: wff ps
  assume prvlem1.1: |- ( ph -> ps )


  assert |- ( Prv ph -> Prv ps )

  proof
    wph
    wps
    wi
    #
    cprvb
    wph
    cprvb
    wps
    cprvb
    wi
    @0
    prvlem1.1
    ax-prv1
    wph
    wps
    ax-prv2
    ax-mp
end
