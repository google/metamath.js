include "wb.mm"
include "wn.mm"
include "wi.mm"
include "wnan.mm"
include "imbi1.mm"
include "wl-dfnan2.mm"
include "3bitr4g.mm"

theorem wl-nanbi1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> ps ) -> ( ( ph -/\ ch ) <-> ( ps -/\ ch ) ) )

  proof
    wph
    wps
    wb
    wph
    wch
    wn
    #
    wi
    wps
    @0
    wi
    wph
    wch
    wnan
    wps
    wch
    wnan
    wph
    wps
    @0
    imbi1
    wph
    wch
    wl-dfnan2
    wps
    wch
    wl-dfnan2
    3bitr4g
end
