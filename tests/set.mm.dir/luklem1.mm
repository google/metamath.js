include "wi.mm"
include "luk-1.mm"
include "ax-mp.mm"

theorem luklem1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume luklem1.1: |- ( ph -> ps )
  assume luklem1.2: |- ( ps -> ch )


  assert |- ( ph -> ch )

  proof
    wps
    wch
    wi
    #
    wph
    wch
    wi
    #
    luklem1.2
    wph
    wps
    wi
    @0
    @1
    wi
    luklem1.1
    wph
    wps
    wch
    luk-1
    ax-mp
    ax-mp
end
