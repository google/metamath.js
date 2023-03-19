include "wnan.mm"
include "bicomi.mm"
include "nanbi1i.mm"
include "mpbi.mm"

theorem nabi1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume nabi1i.1: |- ( ph <-> ps )
  assume nabi1i.2: |- ( ps -/\ ch )


  assert |- ( ph -/\ ch )

  proof
    wps
    wch
    wnan
    wph
    wch
    wnan
    nabi1i.2
    wps
    wph
    wch
    wph
    wps
    nabi1i.1
    bicomi
    nanbi1i
    mpbi
end
