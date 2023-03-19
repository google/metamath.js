include "wxo.mm"
include "whad.mm"
include "xorcom.mm"
include "biid.mm"
include "xorbi12i.mm"
include "df-had.mm"
include "3bitr4i.mm"

theorem hadcoma
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( hadd ( ph , ps , ch ) <-> hadd ( ps , ph , ch ) )

  proof
    wph
    wps
    wxo
    #
    wch
    wxo
    wps
    wph
    wxo
    #
    wch
    wxo
    wph
    wps
    wch
    whad
    wps
    wph
    wch
    whad
    @0
    @1
    wch
    wch
    wph
    wps
    xorcom
    wch
    biid
    xorbi12i
    wph
    wps
    wch
    df-had
    wps
    wph
    wch
    df-had
    3bitr4i
end
