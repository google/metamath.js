include "con4d.mm"
include "impbid.mm"

theorem impcon4bid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
