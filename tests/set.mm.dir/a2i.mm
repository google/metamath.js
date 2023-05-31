include "wi.mm"
include "ax-2.mm"
include "ax-mp.mm"

theorem a2i
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume a2i.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ( ph -> ps ) -> ( ph -> ch ) )

  proof
    wph
    wps
    wch
    wi
    wi
    wph
    wps
    wi
    wph
    wch
    wi
    wi
    a2i.1
    wph
    wps
    wch
    ax-2
    ax-mp
end
