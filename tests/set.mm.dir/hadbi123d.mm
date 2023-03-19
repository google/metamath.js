include "wxo.mm"
include "whad.mm"
include "xorbi12d.mm"
include "df-had.mm"
include "3bitr4g.mm"

theorem hadbi123d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume hadbid.1: |- ( ph -> ( ps <-> ch ) )
  assume hadbid.2: |- ( ph -> ( th <-> ta ) )
  assume hadbid.3: |- ( ph -> ( et <-> ze ) )


  assert |- ( ph -> ( hadd ( ps , th , et ) <-> hadd ( ch , ta , ze ) ) )

  proof
    wph
    wps
    wth
    wxo
    #
    wet
    wxo
    wch
    wta
    wxo
    #
    wze
    wxo
    wps
    wth
    wet
    whad
    wch
    wta
    wze
    whad
    wph
    @0
    @1
    wet
    wze
    wph
    wps
    wch
    wth
    wta
    hadbid.1
    hadbid.2
    xorbi12d
    hadbid.3
    xorbi12d
    wps
    wth
    wet
    df-had
    wch
    wta
    wze
    df-had
    3bitr4g
end
