include "wa.mm"
include "wxo.mm"
include "wo.mm"
include "wcad.mm"
include "ancom.mm"
include "xorcom.mm"
include "anbi2i.mm"
include "orbi12i.mm"
include "df-cad.mm"
include "3bitr4i.mm"

theorem cadcoma
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( cadd ( ph , ps , ch ) <-> cadd ( ps , ph , ch ) )

  proof
    wph
    wps
    wa
    #
    wch
    wph
    wps
    wxo
    #
    wa
    #
    wo
    wps
    wph
    wa
    #
    wch
    wps
    wph
    wxo
    #
    wa
    #
    wo
    wph
    wps
    wch
    wcad
    wps
    wph
    wch
    wcad
    @0
    @3
    @2
    @5
    wph
    wps
    ancom
    @1
    @4
    wch
    wph
    wps
    xorcom
    anbi2i
    orbi12i
    wph
    wps
    wch
    df-cad
    wps
    wph
    wch
    df-cad
    3bitr4i
end
