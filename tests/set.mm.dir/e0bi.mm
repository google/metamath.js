include "mpbi.mm"

theorem e0bi
  let wph: wff ph
  let wps: wff ps
  assume e0bi.1: |- ph
  assume e0bi.2: |- ( ph <-> ps )


  assert |- ps

  proof
    wph
    wps
    e0bi.1
    e0bi.2
    mpbi
end
