include "wn.mm"
include "wi.mm"
include "a1bi.mm"
include "con2b.mm"
include "bitri.mm"

theorem mt2bi
  let wph: wff ph
  let wps: wff ps
  assume mt2bi.1: |- ph


  assert |- ( -. ps <-> ( ps -> -. ph ) )

  proof
    wps
    wn
    #
    wph
    @0
    wi
    wps
    wph
    wn
    wi
    wph
    @0
    mt2bi.1
    a1bi
    wph
    wps
    con2b
    bitri
end
