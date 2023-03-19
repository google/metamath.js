include "wo.mm"
include "orc.mm"
include "wn.mm"
include "wi.mm"
include "orel2.mm"
include "ax-mp.mm"
include "impbii.mm"

theorem biorfi
  let wph: wff ph
  let wps: wff ps
  assume biorfi.1: |- -. ph


  assert |- ( ps <-> ( ps \/ ph ) )

  proof
    wps
    wps
    wph
    wo
    #
    wps
    wph
    orc
    wph
    wn
    @0
    wps
    wi
    biorfi.1
    wph
    wps
    orel2
    ax-mp
    impbii
end
