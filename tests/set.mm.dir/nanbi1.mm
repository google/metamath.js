include "wb.mm"
include "wa.mm"
include "wn.mm"
include "wnan.mm"
include "anbi1.mm"
include "notbid.mm"
include "df-nan.mm"
include "3bitr4g.mm"

theorem nanbi1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> ps ) -> ( ( ph -/\ ch ) <-> ( ps -/\ ch ) ) )

  proof
    wph
    wps
    wb
    #
    wph
    wch
    wa
    #
    wn
    wps
    wch
    wa
    #
    wn
    wph
    wch
    wnan
    wps
    wch
    wnan
    @0
    @1
    @2
    wph
    wps
    wch
    anbi1
    notbid
    wph
    wch
    df-nan
    wps
    wch
    df-nan
    3bitr4g
end
