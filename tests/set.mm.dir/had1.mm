include "whad.mm"
include "wb.mm"
include "hadrot.mm"
include "hadbi.mm"
include "bitri.mm"
include "biass.mm"
include "mpbir.mm"
include "biimpri.mm"

theorem had1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ph -> ( hadd ( ph , ps , ch ) <-> ( ps <-> ch ) ) )

  proof
    wph
    wps
    wch
    whad
    #
    wps
    wch
    wb
    #
    wb
    #
    wph
    @2
    wph
    wb
    @0
    @1
    wph
    wb
    #
    wb
    @0
    wps
    wch
    wph
    whad
    @3
    wph
    wps
    wch
    hadrot
    wps
    wch
    wph
    hadbi
    bitri
    @0
    @1
    wph
    biass
    mpbir
    biimpri
end
