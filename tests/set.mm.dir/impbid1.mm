include "wi.mm"
include "a1i.mm"
include "impbid.mm"

theorem impbid1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume impbid1.1: |- ( ph -> ( ps -> ch ) )
  assume impbid1.2: |- ( ch -> ps )


  assert |- ( ph -> ( ps <-> ch ) )

  proof
    wph
    wps
    wch
    impbid1.1
    wch
    wps
    wi
    wph
    impbid1.2
    a1i
    impbid
end
