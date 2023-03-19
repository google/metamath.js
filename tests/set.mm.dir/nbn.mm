include "wb.mm"
include "wn.mm"
include "bibif.mm"
include "ax-mp.mm"
include "bicomi.mm"

theorem nbn
  let wph: wff ph
  let wps: wff ps
  assume nbn.1: |- -. ph


  assert |- ( -. ps <-> ( ps <-> ph ) )

  proof
    wps
    wph
    wb
    #
    wps
    wn
    #
    wph
    wn
    @0
    @1
    wb
    nbn.1
    wps
    wph
    bibif
    ax-mp
    bicomi
end
