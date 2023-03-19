include "wn.mm"
include "wo.mm"
include "wb.mm"
include "orc.mm"
include "orel2.mm"
include "impbid2.mm"
include "ax-mp.mm"

theorem biorfiOLD
  let wph: wff ph
  let wps: wff ps
  assume biorfi.1: |- -. ph


  assert |- ( ps <-> ( ps \/ ph ) )

  proof
    wph
    wn
    #
    wps
    wps
    wph
    wo
    #
    wb
    biorfi.1
    @0
    wps
    @1
    wps
    wph
    orc
    wph
    wps
    orel2
    impbid2
    ax-mp
end
