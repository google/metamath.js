include "wxo.mm"
include "whad.mm"
include "biid.mm"
include "xorcom.mm"
include "xorbi12i.mm"
include "hadass.mm"
include "3bitr4i.mm"

theorem hadcomb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( hadd ( ph , ps , ch ) <-> hadd ( ph , ch , ps ) )

  proof
    wph
    wps
    wch
    wxo
    #
    wxo
    wph
    wch
    wps
    wxo
    #
    wxo
    wph
    wps
    wch
    whad
    wph
    wch
    wps
    whad
    wph
    wph
    @0
    @1
    wph
    biid
    wps
    wch
    xorcom
    xorbi12i
    wph
    wps
    wch
    hadass
    wph
    wch
    wps
    hadass
    3bitr4i
end
