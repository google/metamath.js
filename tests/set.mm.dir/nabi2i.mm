include "wnan.mm"
include "bicomi.mm"
include "nanbi2i.mm"
include "mpbi.mm"

theorem nabi2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume nabi2i.1: |- ( ph <-> ps )
  assume nabi2i.2: |- ( ch -/\ ps )


  assert |- ( ch -/\ ph )

  proof
    wch
    wps
    wnan
    wch
    wph
    wnan
    nabi2i.2
    wps
    wph
    wch
    wph
    wps
    nabi2i.1
    bicomi
    nanbi2i
    mpbi
end
