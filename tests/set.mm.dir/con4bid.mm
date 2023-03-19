include "wn.mm"
include "biimprd.mm"
include "con4d.mm"
include "biimpd.mm"
include "impcon4bid.mm"

theorem con4bid
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume con4bid.1: |- ( ph -> ( -. ps <-> -. ch ) )


  assert |- ( ph -> ( ps <-> ch ) )

  proof
    wph
    wps
    wch
    wph
    wch
    wps
    wph
    wps
    wn
    #
    wch
    wn
    #
    con4bid.1
    biimprd
    con4d
    wph
    @0
    @1
    con4bid.1
    biimpd
    impcon4bid
end
