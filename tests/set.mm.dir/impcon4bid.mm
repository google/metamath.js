include "con4d.mm"
include "impbid.mm"

theorem impcon4bid
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume impcon4bid.1: |- ( ph -> ( ps -> ch ) )
  assume impcon4bid.2: |- ( ph -> ( -. ps -> -. ch ) )


  assert |- ( ph -> ( ps <-> ch ) )

  proof
    wph
    wps
    wch
    impcon4bid.1
    wph
    wps
    wch
    impcon4bid.2
    con4d
    impbid
end
