include "wa.mm"
include "wxo.mm"
include "wo.mm"
include "wcad.mm"
include "anbi12d.mm"
include "xorbi12d.mm"
include "orbi12d.mm"
include "df-cad.mm"
include "3bitr4g.mm"

theorem cadbi123d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume cadbid.1: |- ( ph -> ( ps <-> ch ) )
  assume cadbid.2: |- ( ph -> ( th <-> ta ) )
  assume cadbid.3: |- ( ph -> ( et <-> ze ) )


  assert |- ( ph -> ( cadd ( ps , th , et ) <-> cadd ( ch , ta , ze ) ) )

  proof
    wph
    wps
    wth
    wa
    #
    wet
    wps
    wth
    wxo
    #
    wa
    #
    wo
    wch
    wta
    wa
    #
    wze
    wch
    wta
    wxo
    #
    wa
    #
    wo
    wps
    wth
    wet
    wcad
    wch
    wta
    wze
    wcad
    wph
    @0
    @3
    @2
    @5
    wph
    wps
    wch
    wth
    wta
    cadbid.1
    cadbid.2
    anbi12d
    wph
    wet
    wze
    @1
    @4
    cadbid.3
    wph
    wps
    wch
    wth
    wta
    cadbid.1
    cadbid.2
    xorbi12d
    anbi12d
    orbi12d
    wps
    wth
    wet
    df-cad
    wch
    wta
    wze
    df-cad
    3bitr4g
end
