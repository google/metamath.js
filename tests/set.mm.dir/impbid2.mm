include "impbid1.mm"
include "bicomd.mm"

theorem impbid2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume impbid2.1: |- ( ps -> ch )
  assume impbid2.2: |- ( ph -> ( ch -> ps ) )


  assert |- ( ph -> ( ps <-> ch ) )

  proof
    wph
    wch
    wps
    wph
    wch
    wps
    impbid2.2
    impbid2.1
    impbid1
    bicomd
end
